"""
EffiCuts

Author: Jan Faron <xfaron01@stud.fit.vutbr.cz>
Date 4.3.2013
This algorithm using some of Marek Visnovsky <xvisno00@stud.fit.vutbr.cz> hypercuts code
"""

import copy
import math
from netbench.classification.maskedint import *
from netbench.classification.prefixset import *
from netbench.classification.algorithms import bclassification
from netbench.classification.ruleset import *


class Header(object):
    """
    Class for header representation in Node
    """
    def __init__(self):
        """
        Constructor
        """
        # Cuts in this node
        self._cuts = {}
        # Is node a leaf?
        self._is_leaf = False
        # Is node use equi-dense or equi-sized cuts?
        self._equi_dense = True
        # Array of indexes to childs
        self._index_array = []
        
    def get_cuts(self):
        """
        Returns cuts applied on node
        """
        return self._cuts

    def is_leaf(self):
        """
        Return True if node is leaf
        """
        return self._is_leaf

class Node(object):
    """
    Class for node representation in EffiCuts tree
    """
    def __init__(self, region = None):
        """
        Constructor
        
        region: dictionary of rule fields ranges
        """        
        # Header
        self._header = Header()
        # Region described by node
        self._region = region
        # Pointers to child nodes
        self._childs = []
        # Rules if node is leaf
        self._rules = RuleSet()
        
    
    def get_header(self):
        """
        Return header of node
        """
        return self._header
    
   
    def add_rules(self, ruleset):
        """
        Add rules stored in node
        
        ruleset: RuleSet containing rules for this node
        """
        self._rules = ruleset
    
    
    def get_rules(self):
        """
        Returns rules in node
        """
        return self._rules
        
    def add_index(self, index):
        """
        Add starting index of child
        """
        self._header._index_array.append(index)
        
    def match(self, packetheader):
        """
        Returns list of rules matching the packet header
        """
        return self._rules.classify(packetheader)
        
    def add_child(self, node, header = False):
        """
        Adds node into the list of childs
        
        node: child to add
        header: header of child
        """
        if header:
            self._childs.append(header)
        self._childs.append(node)
        
    def is_equi_dense(self):
        """
        Return True if equi-dense cuts is used
        """
        return self._header._equi_dense
    
    def get_child(self, index):
        """
        Returns child or header of child and child on specified index
        
        index: index to childs array
        """
        if self.is_equi_dense():
            for i in xrange(len(self._header._index_array)):
                if self._header._index_array[i] > index:
                    index = i - 1
                    index *= 2
                    return self._childs[index], self._childs[index+1]
            index = len(self._header._index_array) - 1
            index *= 2
            return self._childs[index], self._childs[index+1]
        else:
            return False, self._childs[index]
        
    
    def get_childs(self):
        """
        Returns childs of the node
        """
        return self._childs
    
    def count_childs(self):
        """
        Returns number of childs
        """
        return len(self._childs)
    
    def get_region(self):
        """
        Returns nodes region
        """
        return self._region
    
    def set_number_of_cuts(self, nc):
        """
        Stores number of cuts in this node
        
        nc: dictionary of number of cuts
        """
        self._header._cuts = nc
        
    def get_cuts(self):
        """
        Returns cuts applied on node
        """
        return self._header._cuts
        
    def set_leaf(self):
        """
        Determine that node is leaf
        """
        self._header._is_leaf = True
    
    def is_leaf(self):
        """
        Return True if node is leaf
        """
        return self._header._is_leaf
        
    def set_equi_size_cuts(self):
        """
        Set equi-size cuts
        """
        self._header._equi_dense = False
        
    def len_of_index_array(self):
        """
        Return length of index_array
        """
        return len(self._header._index_array)
        

              
class Child(object):
    """
    Child class for Tree in EffiCuts algorithm
    """
    def __init__(self, region, ruleset, bucket_size = 16):
        """
        Constructor
        
        region: region
        ruleset: rules
        bucket_size: maximum number of rules in leaf nodes
        """
        # Region
        self.region = region
        # Rules
        self.ruleset = ruleset
        # Maximum number of rules in leaf nodes
        self.bucket_size = bucket_size
        
    def is_leaf(self):
        """
        Return True if child will be leaf
        """
        if self.ruleset.count_rules() <= self.bucket_size:
            return True
        return False
        
    def get_region(self):
        """
        Return region of child
        """
        return self.region
        
    def get_ruleset(self):
        """
        Return rules of child
        """
        return self.ruleset
        
    def is_empty(self):
        """
        Return True if child has no rules
        """
        if self.ruleset.count_rules() == 0:
            return True
        return False
        

class Tree(object):
    """
    Tree structure for EffiCuts algorithm
    """
    # Constants for statistics in bytes
    NODE_HEADER = 2
    RULE_SIZE = 13
    REGION_BOUNDARY = 16
    CHILDP_SIZE = 4
    # helper list for keeping dimensions in order
    fields_in_order = ["srcipv4", "dstipv4", "protocol", "src_port", "dst_port"]
    
    def __init__(self, spfac = 8, bucket_size = 16, max_cuts = 8):
        """
        Constructor
        """
        # Maximum number of rules in leaf nodes
        self._bucket_size = bucket_size
        # Space factor
        self._spfac = spfac
        # Maximum equi dense cuts
        self._max_cuts = max_cuts
        # Initialization of root
        self._root = None
        # Offsets for region description
        self._offsets = None
        # Heuristics
        self._heuristics = {"push_rules": False, "node_merge": True}
        # Tree statistics
        self._statistics = {"n_of_nodes": 0, "depth": 0, "size": 0, "leafs": 0, "fused_leaves": 0, "fused_nodes": 0, "merged_nodes": 0, "equi_sized_cuts": 0, "equi_dense_cuts": 0, "n_of_rules": 0}
        # Empty node
        self._empty_node = Node(None)
        self._empty_node.set_leaf()
        # Helper list for node merging, contains tuples (child, parent, index)
        self._leafs = []
        
        
        
    def _choose_dimensions(self, ruleset):
        """
        Choose dimensions to cut according to its number of
        unique elements. Returns list of chosen dimensions
        
        ruleset: rules
        """
        mean = 0
        unique = { "srcipv4": [], "dstipv4": [], "protocol": [],
                        "src_port": [], "dst_port": [] }
                
        for rule in ruleset.get_rules():
            for condition in unique.iterkeys():
                try:
                    if not (rule.get_condition(condition) in unique[condition]):
                        unique[condition].append(rule.get_condition(condition))
                except KeyError:
                    pass

        for condition in unique.iterkeys():
            mean += len(unique[condition])
        mean /= 5.0
        
        return [field for field in unique.iterkeys() if len(unique[field]) > mean]
    
    def _optimum_nc(self, dimension, ruleset, region):
        """
        Returns optimum number of cuts in given dimension
        
        dimennsion: cut dimenstion
        ruleset: rules
        region: region to cut
        """
        # statistics about number of cuts
        nc = {"number": 0, "mean": 0, "max": 0, "empty": 0}
        # stack for future heuristics
        stack = []

        value, mask = region.get_data()
        offset = sum([1 for i in bin(mask) if i == "1"])
        domain_size = region.get_domain_size()
        
        for nc["number"] in xrange(1, domain_size - offset):
            cut = []
            for i in xrange(int(math.pow(2, nc["number"]))):
                cut.append(0)
                new_value = value >> (domain_size - offset - nc["number"])
                new_value |= i
                new_value = new_value << (domain_size - offset - nc["number"])
                new_mask = sum([int(math.pow(2, j)) for j in xrange(domain_size - offset - nc["number"], domain_size)])
                # region of current part of new cut
                new_region = MaskedInt(new_value, new_mask, domain_size)
                # number of rules in current part of new cut
                for rule in ruleset.get_rules():
                    try:
                        condition = rule.get_condition(dimension)
                        # PrefixSet
                        if isinstance(condition, PrefixSet):
                            for c in xrange(len(condition)):
                                if condition[c].covers(new_region) or new_region.covers(condition[c]):
                                    cut[i] += 1
                                    break
                        # Int
                        else:
                            for c in xrange(len(condition)):
                                if new_region.covers(MaskedInt(condition[c], None, domain_size)):
                                    cut[i] += 1
                                    break
                    except KeyError:
                        cut[i] += 1
            nc["mean"] = sum(cut) / math.pow(2, nc["number"])          
            nc["max"] = max(cut)
            nc["empty"] = len([x for x in cut if x == 0])
            
            # here comes comparing function, for now simple comparisons
            if len(stack) != 0:
                if float(stack[0]["empty"]) > 0 and nc["empty"] / float(stack[0]["empty"]) >= 2:
                    return stack[0]["number"]
                if nc["mean"] / float(stack[0]["mean"]) > 0.9:
                    return stack[0]["number"]
            stack.insert(0, copy.deepcopy(nc))
            
        return nc["number"]
    
    def _cut(self, region, cut, number_of_bits):
        """
        Make cut-th cut of region on selected number_of_bits
        
        region: region to cut
        cut: number of cut
        number_of_bits: bits used for cutting
        """        
        if number_of_bits == 0:
            return region
        
        value, mask = region.get_data()
        offset = sum([1 for i in bin(mask) if i == "1"])
        domain_size = region.get_domain_size()
        
        new_value = value >> (domain_size - offset - number_of_bits)
        new_value |= cut
        new_value = new_value << (domain_size - offset - number_of_bits)
        new_mask = sum([int(math.pow(2, i)) for i in xrange(domain_size - offset - number_of_bits, domain_size)])
        
        return MaskedInt(new_value, new_mask, domain_size)
    
    def _rules_for_region(self, region, ruleset):
        """
        Extract rules for specified region
        
        region: region to cover
        ruleset: rules to extract
        """
        new_ruleset = RuleSet()

        for rule in ruleset.get_rules():
            acc_cond = 0
            for dimension in region.iterkeys():
                try:
                    condition = rule.get_condition(dimension)
                    # PrefixSet
                    if isinstance(condition, PrefixSet):
                        for c in xrange(len(condition)):
                            if condition[c].covers(region[dimension]) or region[dimension].covers(condition[c]):
                                acc_cond += 1
                                break
                    # Int
                    else:
                        for c in xrange(len(condition)):
                            if region[dimension].covers(MaskedInt(condition[c], None, region[dimension].get_domain_size())):
                                acc_cond += 1
                                break
                except KeyError:
                    acc_cond += 1
            if acc_cond == 5:
                new_ruleset.add_rule(rule)
                
        return new_ruleset        

    def _merge_nodes(self):
        """
        Merges same nodes together
        """    
        merged = []
        for i in xrange(len(self._leafs)):
            if self._leafs[i][0] in merged:
                continue
            current_rules = self._leafs[i][0].get_rules()
            for j in xrange(i + 1, len(self._leafs)):
                if current_rules.count_rules() == self._leafs[j][0].get_rules().count_rules():
                    to_merge = True
                    similar_rules = self._leafs[j][0].get_rules()
                    for k in xrange(current_rules.count_rules()):
                        if current_rules.get_rule(k) != similar_rules.get_rule(k):
                            to_merge = False
                            break
                    # Merge nodes
                    if to_merge:
                        # Change parents pointer
                        self._leafs[j][1].get_childs()[self._leafs[j][2]] = self._leafs[i][0]
                        self._statistics["leafs"] -= 1
                        self._statistics["size"] -= Tree.NODE_HEADER + current_rules.count_rules() * Tree.RULE_SIZE
                        self._statistics["merged_nodes"] += 1
                        self._statistics["n_of_rules"] -= current_rules.count_rules()
                        merged.append(self._leafs[j][0])
        # update list of leafs, just in case
        self._leafs = [leaf for leaf in self._leafs if leaf[0] not in merged]
        
    def fuse_leaves(self, child1, child2):
        """
        Conservative heuristic to fuse contiguous silbling leaves
        
        child1, child2: contiguous childs of current node
        """
        ruleset1 = child1.get_ruleset()
        ruleset2 = child2.get_ruleset()

        # merge rulesets of both childs
        rules = RuleSet()
        for rule in ruleset1.get_rules():
            rules.add_rule(rule, check=True)
        for rule in ruleset2.get_rules():
            rules.add_rule(rule, check=True)
        
        # condition for merging
        if rules.count_rules() <= self._bucket_size:
            return Child(child1.get_region(), rules)
        return False
        
    def fuse_nodes(self, child1, child2, max_rules, nc):
        """
        Moderate heuristic to fuse contiguous silbling non-leaf nodes
        
        child1, child2: contiguous childs of current node
        max_rules: maximum number of rules among all siblings
        nc: number of cuts
        """
        
        ruleset1 = child1.get_ruleset()
        ruleset2 = child2.get_ruleset()
        # merge rulesets of both childs
        rules = RuleSet()
        for rule in ruleset1.get_rules():
            rules.add_rule(rule, check=True)
        for rule in ruleset2.get_rules():
            rules.add_rule(rule, check=True)
        
        # condition for merging
        if rules.count_rules() < max(ruleset1.count_rules() + ruleset2.count_rules(), max_rules):
            region1 = child1.get_region()
            region2 = child2.get_region()
            # region merging
            for field in self.fields_in_order:
                value1, mask = region1[field].get_data()
                value2, mask2 = region2[field].get_data()
                
                if value1 != value2:
                    domain_size = region1[field].get_domain_size()
                    offset = sum([1 for i in bin(mask) if i == "1"])
                    i = 0
                    while value1 != value2:
                        mask >>= (domain_size - offset + i)
                        mask <<= (domain_size - offset + i)
                        value1 &= mask
                        value2 &= mask
                        i += 1
                    region1[field] = MaskedInt(value1, mask, domain_size)
                
            return Child(region1, rules)
        return False

    def get_max_rules(self, childs):
        """
        Return maximum rules of all siblings
        
        childs: childs of current node
        """
        max = 0
        for child in childs:
            count = child.get_ruleset().count_rules()
            if count > max:
                max = count
        return max 
    
    def equi_dense_cuts(self, ruleset, region, depth = 0):
        """
        Equi-dense cuts
        
        ruleset: rules
        region: region to cut
        depth: total depth of tree
        """
        node = Node()

        # choose dimensions to cut
        dim = self._choose_dimensions(ruleset)
        
        # determine number of cuts in chosen dimensions
        max_childs = self._spfac * math.sqrt(ruleset.count_rules())
        
        # optimal number of cuts in each dimension
        nc = { "srcipv4": 0, "dstipv4": 0, "protocol": 0,
                        "src_port": 0, "dst_port": 0 }
        # number of cuts
        n = 1
        #determine optimal number of cuts (in our case bits)
        for i in dim:
            nc[i] = self._optimum_nc(i, ruleset, region[i])
            n *= math.pow(2, nc[i])
            
        # remove excess cuts
        while n > max_childs:
            for i in dim:
                if nc[i] >= 1:
                    n /= math.pow(2, nc[i])
                    nc[i] -= 1
                    n *= math.pow(2, nc[i])
                if n <= max_childs:
                    break

        # save number of cuts
        node.set_number_of_cuts(nc)

        # field that store childs of current node
        childs = []
        # cutting current region into the pieces
        new_region = {}
        for i in xrange(int(math.pow(2, nc["srcipv4"]))):
            new_region["srcipv4"] = self._cut(region["srcipv4"], i, nc["srcipv4"])            
            for j in xrange(int(math.pow(2, nc["dstipv4"]))):
                new_region["dstipv4"] = self._cut(region["dstipv4"], j, nc["dstipv4"])
                for k in xrange(int(math.pow(2, nc["protocol"]))):
                    new_region["protocol"] = self._cut(region["protocol"], k, nc["protocol"])
                    for l in xrange(int(math.pow(2, nc["src_port"]))):
                        new_region["src_port"] = self._cut(region["src_port"], l, nc["src_port"])
                        for m in xrange(int(math.pow(2, nc["dst_port"]))):
                            new_region["dst_port"] = self._cut(region["dst_port"], m, nc["dst_port"])
                            # new ruleset of new region
                            new_ruleset = self._rules_for_region(new_region, ruleset)
                            # store new region
                            new_region_copy = copy.deepcopy(new_region)
                            childs.append(Child(new_region_copy, new_ruleset))

        fused_leaves = 0
        fused_nodes = 0
        max_rules = self.get_max_rules(childs)
        index = 0
        node.add_index(0)
        # merging childs
        for i in xrange(len(childs) - 1):
            if node.len_of_index_array() > self._max_cuts:
                return False, 0

            if childs[index].is_empty():
                childs.pop(index)
                continue
            if childs[index+1].is_empty():
                childs.pop(index+1)
                continue
            # if both childs will be leaves
            if childs[index].is_leaf() and childs[index+1].is_leaf():
                new_child = self.fuse_leaves(childs[index], childs[index+1])
                if new_child:
                    childs.pop(index)
                    childs.pop(index)
                    childs.insert(index, new_child)
                    fused_leaves += 1 
                else:
                    node.add_index(i+1)
                    index += 1
                    
            # if both childs will be internal nodes
            elif not childs[index].is_leaf() and not childs[index+1].is_leaf():
                new_child = self.fuse_nodes(childs[index], childs[index+1], max_rules, nc)
                if new_child:
                    childs.pop(index)
                    childs.pop(index)
                    childs.insert(index, new_child)
                    fused_nodes += 1 
                else:
                    node.add_index(i+1)
                    index += 1
            else:
                node.add_index(i+1)
                index += 1
                
        if node.len_of_index_array() > self._max_cuts:
            # switch back to equi size cuts
            return False, 0

        # creating new child nodes
        for child in childs:
            child, childs_depth = self.create_node(child.get_ruleset(), child.get_region())
            if childs_depth > depth:
                depth = childs_depth
            child_header = child.get_header()
            # store child and header of the child
            node.add_child(child, child_header)

        # actualize statistics
        self._statistics["size"] += Tree.NODE_HEADER + node.len_of_index_array() * (Tree.CHILDP_SIZE + Tree.NODE_HEADER)
        self._statistics["n_of_nodes"] += 1
        self._statistics["fused_nodes"] += fused_nodes
        self._statistics["fused_leaves"] += fused_leaves
        self._statistics["equi_dense_cuts"] += 1
        
        depth += 1
        
        return node, depth
        
    def equi_sized_cuts(self, ruleset, region, depth = 0):
        """
        Equi sized cuts
        """
        #region = self.region_compaction(region)
        
        node = Node(region)
        node.set_equi_size_cuts()
        
        # choose dimensions to cut
        dim = self._choose_dimensions(ruleset)
        
        # determine number of cuts in chosen dimensions
        max_childs = self._spfac * math.sqrt(ruleset.count_rules())
        
        # optimal number of cuts in each dimension
        nc = { "srcipv4": 0, "dstipv4": 0, "protocol": 0,
                        "src_port": 0, "dst_port": 0 }
        # number of cuts
        n = 1
        # determine optimal number of cuts (in our case bits)
        for i in dim:
            nc[i] = self._optimum_nc(i, ruleset, region[i])
            n *= math.pow(2, nc[i])
            
        # remove excess cuts
        while n > max_childs:
            for i in dim:
                if nc[i] >= 1:
                    n /= math.pow(2, nc[i])
                    nc[i] -= 1
                    n *= math.pow(2, nc[i])
                if n <= max_childs:
                    break

        # save number of cuts
        node.set_number_of_cuts(nc)
        
        # cutting current region into the pieces
        new_region = {}
        for i in xrange(int(math.pow(2, nc["srcipv4"]))):
            new_region["srcipv4"] = self._cut(region["srcipv4"], i, nc["srcipv4"])            
            for j in xrange(int(math.pow(2, nc["dstipv4"]))):
                new_region["dstipv4"] = self._cut(region["dstipv4"], j, nc["dstipv4"])
                for k in xrange(int(math.pow(2, nc["protocol"]))):
                    new_region["protocol"] = self._cut(region["protocol"], k, nc["protocol"])
                    for l in xrange(int(math.pow(2, nc["src_port"]))):
                        new_region["src_port"] = self._cut(region["src_port"], l, nc["src_port"])
                        for m in xrange(int(math.pow(2, nc["dst_port"]))):
                            new_region["dst_port"] = self._cut(region["dst_port"], m, nc["dst_port"])
                            new_ruleset = self._rules_for_region(new_region, ruleset)
                            child, childs_depth = self.create_node(new_ruleset, new_region)
                            if childs_depth > depth:
                                depth = childs_depth
                            node.add_child(child)
                            # for node merging
                            if child.is_leaf() and child is not self._empty_node:
                                self._leafs.append((child, node, node.count_childs() - 1))
        
        # actualize statistics
        self._statistics["size"] += Tree.NODE_HEADER + Tree.REGION_BOUNDARY + n * Tree.CHILDP_SIZE
        self._statistics["n_of_nodes"] += 1
        self._statistics["equi_sized_cuts"] += 1
        
        depth += 1
        
        return node, depth
    
    def create_node(self, ruleset, region, depth = 0):
        """
        Creates node and its childs recursively
        """
        
        # if there are too few rules, we consider node a leaf 
        if ruleset.count_rules() <= self._bucket_size:
            node = Node()
            if ruleset.count_rules() == 0:
                node = self._empty_node
                return node, 1
            node.set_leaf()
            node.add_rules(ruleset)
            self._statistics["leafs"] += 1
            self._statistics["size"] += Tree.NODE_HEADER + Tree.RULE_SIZE * ruleset.count_rules()
            self._statistics["n_of_rules"] += ruleset.count_rules()
            return node, 1
            
        # trying equi-dense cuts
        node, childs_depth = self.equi_dense_cuts(ruleset, region)
        if node == False:
            node, childs_depth = self.equi_sized_cuts(ruleset, region)
        
        if childs_depth > depth:
                depth = childs_depth
        return node, depth
        
    
    def build_tree(self, ruleset):
        """
        Builds Tree for EffiCuts
        
        ruleset: rules for tree
        """
        
        # Definition of initial region
        initial_region = { "srcipv4": MaskedInt(0, 0, 32), "dstipv4": MaskedInt(0, 0, 32),
                           "protocol": MaskedInt(0, 0, 8), "src_port": MaskedInt(0, 0, 16),
                           "dst_port": MaskedInt(0, 0, 16) }

        self._root, self._statistics["depth"] = self.create_node(ruleset, initial_region)
        
        # Node merging
        if self._heuristics["node_merge"]:
            self._merge_nodes()
            
        return self._statistics
            
    def process_packet_header(self, packetheader):
        """
        Preprocess packet header for classification
        
        packetheader: packet to preprocess
        """
        header = {}
        
        if packetheader.get_header("ipv4") is None:
            return None
        else:
            header["srcipv4"] = MaskedInt(packetheader["ipv4"].get_field("src_addr"), 0, 32)
            header["dstipv4"] = MaskedInt(packetheader["ipv4"].get_field("dst_addr"), 0, 32)
            header["protocol"] = MaskedInt(packetheader["ipv4"].get_field("protocol"), 0, 8)
            protocol_field = packetheader["ipv4"].get_field("protocol").toStr().lower()
            header["dst_port"] = MaskedInt(packetheader[protocol_field].get_field("dst_port"), 0, 16)
            header["src_port"] = MaskedInt(packetheader[protocol_field].get_field("src_port"), 0, 16)
            return header
            
    def search_tree(self, packet_header):
        """
        Searchs Tree for coressponding rules
        
        packet_header: packet header to search matching rules
        """
        matching_rules = []
        packet_region = self.process_packet_header(packet_header)
        if packet_region is None:
            return matching_rules
        current_node = self._root
        header = current_node.get_header()
        
        while not header.is_leaf():
            child_index = 0
            cuts = header.get_cuts()
            for dimension in Tree.fields_in_order:
                if cuts[dimension] > 0:
                    value, mask = packet_region[dimension].get_data()
                    offset = sum([1 for i in bin(mask) if i == "1"])
                    value &= ~mask
                    value >>= (packet_region[dimension].get_domain_size() - offset - cuts[dimension])
                    child_index <<= cuts[dimension]
                    child_index |= value
            header, current_node = current_node.get_child(child_index)   
            if not header:
                header = current_node.get_header()
        
        matching_rules = current_node.match(packet_header)
        
        return matching_rules

    
    def get_stats(self):
        """
        Returns statistics about Tree
        """
        return self._statistics



#######################################################################
# Subcategory class for EffiCuts algorithm
#######################################################################
class Subcategory:
    """
    Subcategory class for heuristics separable trees and selective tree merging
    """
    def __init__(self, regions):
        """
        Constructor
        
        regions: number that determine large and small field in each region
        """
        # Rules
        self._rules = RuleSet()
        # Regions
        self._regions = regions
        
        #if this subcategory was already selected for merging
        self._used = False
        
    def add_rule(self, rule):
        """
        Add rule to subcategory
        
        rule: rule
        """
        self._rules.add_rule(rule)    
    
    def get_regions(self):
        """
        Return regions of subcategory
        """
        return self._regions
     
    def get_rules(self):
        """
        Return rules of subcategory
        """
        return self._rules
        
    def set_used(self):
        """
        If this subcategori was already selected for tree merging
        """
        self._used = True
        
    def is_used(self):
        """
        Return True if this subcategori was already selected for tree merging
        """
        return self._used

#######################################################################
# EffiCuts algorithm class
#######################################################################
class EffiCuts (bclassification.BClassification):
    """
    EffiCuts algorithm for packet classification
    """    
    def __init__(self, spfac = 8, bucket_size = 16):
        """
        Constructor
		
		spfac: space factor
        bucket_size: maximum number of rules that can be stored in leaf node
        """       
		# Space factor
        self._spfac = spfac
        # Maximum number of rules in leaf nodes
        self._bucket_size = bucket_size
        # Rules
        self._rules = RuleSet()
        # Subcategories of 5 categories
        self._categories = [[],[],[],[],[]]
        # Ruleset for each tree
        self._trees_rules = []
        # Trees
        self._trees = []
        # Efficuts statistics
        self._statistics = {"category0": 0, "category1": 0, "category2": 0, "category3": 0, "category4": 0, "merged_trees": 0, "n_of_trees": 0}
        # Statistics of trees
        self._trees_stats = []
        
    def separable_trees(self, ruleset):
        """
        Separate rules into multiple categories and subcategories
        
        ruleset: rules
        """
        
        # approximately 5% of ipv4 region
        largeness_fraction_ipv4 = 214748365
        
        #appriximately 50% of port region
        largeness_fraction_port = 32768

        # foreach region in rule decide whether is large or small and
        # also get indexes of category(index) and subcategory(regions)
        for rule in ruleset.get_rules():
            index = 5
            regions = 0
            range = rule.get_condition('srcipv4')[0].get_range()
            if (range[1] - range[0]) > largeness_fraction_ipv4:
                index -=1
                regions += 10000
                
            range = rule.get_condition('dstipv4')[0].get_range()
            if (range[1] - range[0]) > largeness_fraction_ipv4:
                index -=1
                regions += 1000
            
            range = rule.get_condition('src_port')[0].get_range()
            min = range[0]
            range = rule.get_condition('src_port')[-1].get_range()
            max = range[1]
            if (max - min) > largeness_fraction_port:
                index -=1
                regions += 100
            
            range = rule.get_condition('dst_port')[0].get_range()
            min = range[0]
            range = rule.get_condition('dst_port')[-1].get_range()
            max = range[1]            
            if (max - min) > largeness_fraction_port:
                index -=1
                regions += 10
                
            if rule.get_condition('protocol')[0].get_value() == 0:
                index -=1
                regions += 1
                
			# in category 4 are rules with 0 or 1 large region
            if index == 5:
                index = 4
            
            # add rule to subcategory of category[index]
            found = False
            for subcategory in self._categories[index]:
                if subcategory.get_regions() == regions:
                    subcategory.add_rule(rule)
                    found = True
                    break
            if not found:
                self._categories[index].append(Subcategory(regions))
                self._categories[index][-1].add_rule(rule)
                self._statistics["category" + str(index)] += 1
                

 
    def select_subcategory1(self, index):
        """
        Select subcategory in category[index] that has fewer rules
        Return index of subcategory1
        
        index: index of category
        """
        
        i = 0
        min = 1000000 #some large number
        count = 0
        min_i = 0
        for subcategory in self._categories[index]:
            if subcategory.is_used():
                i += 1
                continue
            count = subcategory.get_rules().count_rules()
            if count < min:
                min = count
                min_i = i
            i += 1
        
        #if there is non subcategory
        if min == 1000000:
            return -1
        return min_i
        
    def select_subcategory2(self, index, regions):
        """
        Select suitable subcategory that has difference in the smallest region 
        
        index: index of category
        regions: regions of subcategory1
        #return index of subcategory2
        """
        i = 0
        min_diff = 1000000 #some large number
        min_i = 0
        for subcategory in self._categories[index]:
            sub_regions = subcategory.get_regions()
            diff = max(regions, sub_regions) - min(regions, sub_regions)
			# only 1 region must be different (smaller region si better)
            if (diff == 10000) or (diff == 1000) or (diff == 100) or (diff == 10) or (diff == 1):
                if diff < min_diff:
                    min_diff = diff
                    min_i = i
                i += 1
        
        # if there is non suitable subcategory
        if min_diff == 1000000:
            return -1
        return min_i
 
    def selective_tree_merging(self):
        """
        Merge trees in categories
        """

        # starting with category 1 to merge with category 0
        index = 1
        while index < 4:
            # select subcategory in category[index] that has fewer rules
            i_1 = self.select_subcategory1(index)
            # i_1 is index of subcategory (-1 when there is none subcategory left)
            if i_1 == -1:
                index += 1
                continue
            # select suitable subcategory in category[index-1]
            i_2 = self.select_subcategory2(index-1, self._categories[index][i_1].get_regions())
            if i_2 == -1:
                # subcategory1 has not found suitable subcategory2
                self._categories[index][i_1].set_used()
                continue

            # merge subcategories (rules)
            rules = RuleSet()
            for rule in self._categories[index][i_1].get_rules().get_rules():
                rules.add_rule(rule)
            for rule in self._categories[index-1][i_2].get_rules().get_rules():
                rules.add_rule(rule)
            self._trees_rules.append(rules)    
            del self._categories[index][i_1]
            del self._categories[index-1][i_2]
            self._statistics["merged_trees"] += 1
 
        # append rest of unmerged subcategories
        for category in self._categories:
            for subcategory in category:
                self._trees_rules.append(subcategory.get_rules())

    def classify(self, packetheader):
        """
        Classifies packet using EffiCuts algorithm
        
        return: list of rules corresponding to packetheader
        """
        
        final = []
        rules = []
        for tree in self._trees:
            rules = tree.search_tree(packetheader)
            if rules:
                final.extend(rules)
        final.sort(cmp=lambda x,y: cmp(x.get_priority(), y.get_priority()))
        return final
            

    
    def report_memory(self):
        """
        Print statistics about EffiCuts
        """
        #print "EffiCuts categorization"
        #print "Category 0: " + str(self._statistics["category0"]) + " trees"
        #print "Category 1: " + str(self._statistics["category1"]) + " trees"
        #print "Category 2: " + str(self._statistics["category2"]) + " trees"
        #print "Category 3: " + str(self._statistics["category3"]) + " trees"
        #print "Category 4: " + str(self._statistics["category4"]) + " trees"
        #print "Merged trees: " + str(self._statistics["merged_trees"])
        #print "Total number of trees " + str(self._statistics["n_of_trees"])
        
        summary = {"i": 0, "n_of_nodes": 0, "depth": 0, "size": 0, "leafs": 0, "fused_leaves": 0, "fused_nodes": 0, "merged_nodes": 0, "equi_sized_cuts": 0, "equi_dense_cuts": 0, "n_of_rules": 0}
        i = 1
        for tree in self._trees_stats:
            #print "\nTree " + str(i)
            summary["i"] = i
            #print "Number of internal nodes: " + str(tree["n_of_nodes"])
            summary["n_of_nodes"] += tree["n_of_nodes"]
            #print "Leafs: " + str(tree["leafs"])
            summary["leafs"] += tree["leafs"]
            #print "Depth: " + str(tree["depth"])
            summary["depth"] += tree["depth"]
            #print "Equi-dense cuts: " + str(tree["equi_dense_cuts"])
            summary["equi_dense_cuts"] += tree["equi_dense_cuts"]
            #print "Equi-sized cuts: " + str(tree["equi_sized_cuts"])
            summary["equi_sized_cuts"] += tree["equi_sized_cuts"]
            #print "Merged nodes: " + str(tree["merged_nodes"])
            summary["merged_nodes"] += tree["merged_nodes"]
            #print "Size: " + str(tree["size"])
            summary["size"] += tree["size"]
            #print "Fused_leaves: " + str(tree["fused_leaves"])
            summary["fused_leaves"] += tree["fused_leaves"]
            #print "Fused_nodes: " + str(tree["fused_nodes"])
            summary["fused_nodes"] += tree["fused_nodes"]
            #print "Total rules: " + str(tree["n_of_rules"])
            summary["n_of_rules"] += tree["n_of_rules"]
            i += 1
            
        print "EffiCuts statistics"
        print "\nSummary " + str(summary["i"]) + " trees"
        print "Merged trees: " + str(self._statistics["merged_trees"])
        #print "Number of internal nodes: " + str(summary["n_of_nodes"])
        #print "Leafs: " + str(summary["leafs"])
        print "Depth: " + str(summary["depth"])
        print "Number of nodes: " + str((summary["n_of_nodes"] + summary["leafs"]))
        print "Total Size: " + str(summary["size"])
        print "Total stored rules: " + str(summary["n_of_rules"])
        print "\nEqui-dense cuts: " + str(summary["equi_dense_cuts"])
        print "Equi-sized cuts: " + str(summary["equi_sized_cuts"])
        print "Merged nodes: " + str(summary["merged_nodes"])
        print "Fused_leaves: " + str(summary["fused_leaves"])
        print "Fused_nodes: " + str(summary["fused_nodes"])
        
    
    def load_ruleset(self, ruleset):
        """
        Load ruleset and start EffiCuts algorithm
        """
        regions = ['srcipv4','dstipv4','src_port','dst_port','protocol']

        # copy rules (this operation will remove duplicates and rules
        #             covered by other rules)
        for rule in ruleset.get_rules():
            self._rules.add_rule(rule, check=True)

        self._rules.add_universal_prefixes(regions)

        ruleset = self._rules

        # separate rules into multiple categories and subcategories
        self.separable_trees(ruleset)
        
        # merging trees in categories
        self.selective_tree_merging()
        self._statistics["n_of_trees"] = len(self._trees_rules)
        
        #initializing Trees
        for rules in self._trees_rules:
            self._trees.append(Tree(self._spfac, self._bucket_size))
            self._trees_stats.append(self._trees[-1].build_tree(rules))
            
    
    
