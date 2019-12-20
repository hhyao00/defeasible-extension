def Literal():
    
    def __init__(self, prop, mod, lit):
        """
        A true or false statement of certain modality.
        prop is '+' or '-' E.g: ('-',visit) means we do
        not visit. Mod isa {belief, obligation, desire, goal,
        intention} and  
        
        """
        self.prop = prop
        self.mod = mod
        self.lit = lit
        
    def complement(self):
        """ 
        Return the complement of the literal. Example:
        complement of ('+',G,"visit") is ('-',G,"visit")
        """
        if self.prop == '+':
            return ('-',mod,lit)
        if self.prop == '-':
            return ('+',mod,lit)
    """ end Literal class """
    
def Rule():

    def __init__(self, modality, antecedent=[], consequent=[], 
                 superiors=set(), inferiors=set()):
        """
        @'modality' mod {belief, obligation, desire, goal, intention,
        outcome, social intention}. A rule of Belief modality is a Fact.
        @'antecedent' is the action/body taken (if), and produces a series
        of consequences @'consequent' from most desireable consequent[0],
        to the least desireable consequent[-1]. Empty antecedent is what
        the cognitive agent believes is true of the world (modality=B).
        @'superiors' are rules that have higher priority than this rule.
        @'inferiors' are rules such that this rule (self) is sueprior.
        
        A rule is identified by its antecedent name, which is a string.
        If the string premise matches with another node's, they must
        either the same node, or a violation. Any c in consequent is
        likewise identified by its name. Consequent c can be a premise
        of a RuleNode.
        
        'antecedent' is the antecedent, or body, if 'antecedent(s)' then 
        'consequent(s)'. 'modality' is the type of consequent. For example,
        if premise=drive_car, and modality=obligation, then consequent[0]=
        not_damage, consequent[1]=pay_damage -- if I drive a car then I have
        the obligation to not crash, if I crash (failure of consequent[0]), 
        then I have the obligation to pay for damage. If consequent is empty,
        then the premise must be true (if there are no consequences to
        doing an action, then there are no reasons to not do it because it
        would be as if it was not done in the first place).
        """
        self.mod = modality
        self.antecedent = antecedent
        self.consequent = consequent
        self.superiors = superiors
        self.inferiors = inferiors
    
    def dominates(self, node=None):
        """ This ruleNode is superior to some other rule node. 
        Beware of cycles. I should condition check this probably """
        if node == None:
            return
        self.inferiors.add(node)
        
    def remove_antecedent(self, a):
        """ remove antecedent from antecent (body) of rule. """
        if a not in self.antecedent: return False
        self.antecedent.remove(a)
        return True
        
    def truncate_consequent(self, c):
        """ c is a consequent. If c is proved, then it must hold
        as the most desirable consequent. In such case, there is no
        need to consider less desirable consequets. We can truncate
        the list of consequents after c. Return true on success. """
        if c not in self.consequent: return False
        idx = self.consequent[c]
        self.consequent = self.consequent[:idx+1]
        return True
    
    def remove_consequent(self, c):
        """ c is a literal to be removed from consequent chain bc
        it no longer can be true, OR because it was proven and we 
        no longer need to consider it """
        if c not in self.consequent: return False
        self.consequent.remove(c)
        return True


def DefeasibleExtension():
    """
    Algorithm class to comput the fixed point extension of
    a defeasible theory, which is given as a set of rules. 
    * Not complete so this should be treated as psuedocode.

    Usage:
    DE = DefeasibleExtension()
    pc, nc = DE.DefeasibleConclusion()

    'pc' and 'nc' are the positive and negative defeasible conclusions.
    A defeasible extension (def. 17 in original paper) {pc} U {nc}.
    """
    
    B = 'B'   # belief
    D = 'D'   # desire
    G = 'G'   # goal
    I = 'I'   # intention
    SI = 'SI' # social intention
    O = 'O'   # obligation
    U = 'U'   # outcome
    MODALITY = {B, O, D, G, I, SI}
    OutcomeMods = [O,G,I,SI]

    def __init__(self, rule_list=[]):
    
        # All rules, where each rule produces 
        # an outcome of modality m in MOD/{U}
        self.Rules = {}
        for m in list(MODS+{U}):
            self.Rules[m] = []

        # Some modalities correspond to goal like attitudes,
        # they produce the byproduct that is Outcome.
        self.R = []     # Rules of modality in {O,GI,I,SI}
        
        # Literals or their complement can ontake certain modalities
        # depending on the provided set of facts/rules/beliefs. And 
        # the Herbrand base which is all the possible literals exist.
        self.LiteralMods = {}
        self.ComplementLiteralMods = {}
        
        # Initalize global and temporary (local) defeasible conclusion sets.
        self.positive_conclusion, self.temp_positive_conclusion = set(),set()
        self.negative_conclusion, self.temp_negative_conclusion = set(),set()

    def Refuted(self, lit, mod):
        """ 
        Algorithm 3 - Refuted. Called to eliminate a literal or its 
        complemented from a consequent chain of rule specific modality.
        'lit' is a Literal that is an instance of abstract form:
        (prop '+' or '-', mod, literal_name). Mod in MODALITY.
        If we are refuting the complement of literal, it is expected that
        lit.complement is passed in as parameter.
        """
        
        self.temp_negative_conclusion.add(lit)
        self.LiteralMods[lit].add(('-',mod))
        self.HerbrandBase.remove(lit)
        
        # Similar to Proved, remove the literal from rule antecedents in
        # attempt to see if we can obtain an empty body for any rule. If
        # the body, or antecedent of a rule is empty, it can fire.
        for r in self.R:
            if lit in r.antecedent:
                if mod in OutcomeMods: 
                    r.remove_antecedent(lit.complement())
            for s in r.superiors:
                r.superiors.remove(s)
                s.inferiors.remove(r)
        for r in self.RB_conv:
            r.remove_antecedent(lit)
        
        # Resolve modalities that affect one another; remove literals that 
        # no longer hold or need to be considered once lit is refuted.
        if mod == B:
            [r.remove_consequent(lit.complement()) for r in self.Rules[I]]
            for r in self.Rules[O]:
                if ('+',O) in self.LiteralMods[lit]: 
                    r.truncate_consequent(lit)
            for r in self.Rules[SI]:
                if ('-',O) in self.LiteralMods[lit]: 
                    r.remove_consequent(lit.complement())
        
        elif mod == O:
            for r in self.Rules[O]:
                r.truncate_consequent(lit)
                r.remove_consequent(lit)
            if ('-',B) in self.LiteralMods[lit]:
                for r in self.Rules[SI]:
                    r.remove_consequent(lit.complement())
        
        elif mod == D:
            [r.truncate_consequent(lit) for r in self.Rules[D]]
            [r.truncate_consequent(lit) for r in self.Rules[G]]
        
        # Otherwise mod is not B or O or D, update for the respective mod
        # by removing the literal from the consequent chain of rule r.
        else:
            for r in self.Rules[mod]:
                r.remove_consequent(lit)
                r.truncate_consequent(lit.complement()) 
        """ end Refuted() """
        
    
    def Proved(self, lit, mod):
        """ 
        Algorithm 2 - Proved. Called when a literal is proved in
        rule with mod in order to reduce complexity of algorithm.
        If we are refuting the complement of literal, it is expected
        that lit.complement() is passed in as parameter.
        """

        # The computation starts by updating:
        # the relative positive extension set for modality ✷ and, symmetrically, 
        # the local information on literal l (line 2); l is then removed from HB
        # at line 3. Parts 1.–3. of Proposition 2 identifies the modalities literal
        # ∼l is refuted with, when ✷l is proved
        
        self.temp_positive_conclusion.add(lit)
        self.LiteralMods[lit].add(('+',mod))
        self.HerbrandBase.remove(lit)
        
        if mod != D: self.Refuted(lit.complement(), mod)
        if mod == B: self.Refuted(lit.complement(), mod)
        if mod in [B,O]: self.Refuted(lit.complement(), SI)

        # Update rule sets and the superior relation for consistency
        # remove rule if the rule appears in the antecendent: this is how
        # we will be able to achieve the "empty body" and fire-able rule.
        mods = [O,G,I,SI]
        for r in self.R:
            if lit in r.antecedent:
                if mod in mods and lit.mod == mod:
                    r.remove_antecedent(lit)
                    r.remove_antecedent(lit.complement())
            for s in r.superiors:
                r.superiors.remove(s)
                s.inferiors.remove(r)
        for r in self.RB_conv:
            r.remove_antecedent(lit)

        # Depending on modality of l, perform specific operations on the chains
        # For mod == Belief, since belief conflicts with O, I, we remove the lit
        # from the consequents of rules of Obligation and Intention outcomes.
        if mod == B:
            for r in self.Rules[O]:
                r.remove_consequent(lit)
                if ('+',O) in self.ComplementLiteralMods[lit]:
                    r.truncate_consequent(lit.complement())
            for r in self.Rules[I]:
                r.remove_consequent(lit)
            for r in self.Rules[SI]:
                if ('-',O) in self.ComplementLiteralMods[lit]:
                    r.remove_consequent(lit)

        # Update all obligation rules, such that we both truncate everything up to
        # and including lit.complement. If mod is Obligation and belief is associated
        # with this literal then remove it from the obligation and social intentions.
        # Basically, updating the conflict relations.
        elif mod == O:
            for r in self.Rules[O]:
                r.truncate_consequent(lit.complement())
                r.remove_consequent(lit.complement())
                if ('-',B) in self.LiteralMods[lit]:
                    r.remove_consequent(lit)
            for r in self.Rules[SI]:
                if ('-',B) in self.ComplementLiteralMods[lit]:
                    r.remove_consequent(lit)

        # Similarly, if it is a +Desire, and it exists in the complement set of litmods,
        # then update our Goals such that the literal is removed from rules that produce
        # goals. Since if a +Desire is in the lit.complement set, but lit has been proven
        # true, then there is no need to consider the existence of +D in lit.complement.
        # since now +D is for sure in the mods that lit can ontake.
        elif mod == D:
            if ('+',D) in self.ComplementLiteralMods[lit]:
                for r in self.Rules[G]:
                    r.truncate_consequent(lit)
                    r.remove_consequent(lit)
                    r.truncate_consequent(lit.complement())
                    r.remove_consequent(lit.complement())

        # Otherwise mod is not B or O or D, update for the respective mod by    
        else:
            for r in self.Rules[mod]:
                r.remove_consequent(lit)
                r.truncate_consequent(lit.complement())        
        """ end Proved() """

        
    def DefeasibleConclusion(self):
        """ Algorithm 1 - DefeasibleExtension in the paper. """  
        
        ## ----- Utility functions ------------------------ ##
        
        def findModConsequents(mod,lit):
            """  find the rules with modality mod 
            and lit in the consequence chain """
            pass
        
        def convertable(lit1, lit2):
            """ A literal is only realizable if the agent 
            -believes- it is. Beliefs tell of the state of the
            world through the eyes of the agent and if a literal
            cannot be reached via a belief rule or chain then 
            it is not achievable. Returns true or false. """
            pass
            
        ## ------------------------------------------------ ## 
        
        # For every outcome rule, the algorithm makes a copy of the
        # same rule for each mode corresponding to a goal-like attitude
        self.R = []
        for r in Rules[U]:
            for mod in [D,G,I,SI]:
                self.R.append(Rule(mod, r.antecedent, r.consequent,
                          r.superiors, r.inferiors))

        # A belief rule producing a consequent c can be converted to
        # another modality, if that other rule produces consequent c.
        # We also pass along the superior relation set since superior
        # is a transitive relationship.
        self.RB_conv = []
        for r in Rules[B]:
            for mod in [O,D,G,I,SI]:
                rules_mod = list(Rules[mod])
                for c0 in r.consequent:
                    for s in rules_mod:
                        if c1 in s.consequent:
                            self.RB_conv.append(Rule(s.mod,r.antecedent,r.consequent,
                                              r.superiors,r.inferiors))

        # What we know, or believe, are facts, are immediately proved.
        for f in self.Facts:
            if f.prop == '+':
                self.Proved(f)
            if f.prop == '-' and f.mod != D:
                self.Refuted(f)

        # Initalize the set of inferior_defeated rules
        # and merge the temporary conclusion sets into the global.
        self.positive_conclusion.append(self.temp_positive_conclusion[:])
        self.negative_conclusion.append(self.temp_negative_conclusion[:])
        R_infd = set()
        while len(self.temp_positive_conclusion) > 0 and \
                len(self.temp_negative_conclusion) > 0:

            self.temp_positive_conclusion = []
            self.temp_negative_conclusion = []

            # For every literal l in HerbrandBase, there must be
            # some way of reaching it given the state of the world (beliefs).
            # If there is no way of reaching, or converting, from a belief
            # to literal l, then it is refuted.
            for l in self.HerbrandBase:
                for r_conv in self.RB_conv:
                    if len(convertable(r_conv,l)) == 0:
                        self.Refuted(l,r_conv.mod)
            #
            AllRules = self.R + self.RB_conv
            for r in AllRules:
                # A rule whose body is not not-empty, is not provable.
                if len(r.antecedent) > 0:
                    continue

                # Iterate on rules that can immediately fire because of an
                # empty body/antecedent/premise. A(r) = {r1..rn} ->x C(r) for
                # some x in MOD. A(r) is set of premises and C(r) is chain.
                # Collect the superior and inferior relations from r.
                r_inf = set(r.inferiors[:])
                r_sup = set(r.superiors[:])
                R_infd = set(R_infd + r_inf[:])

                # l is the firt literal of C(r) in HerbrandBase
                l = r.consequent[0]
                if len(r_sup) != 0:
                    continue
                if r.mod == D:
                    self.Proved(l,D)
                else:   
                    # Refute the complement of l, and collect mods that are the
                    # complment of l and have conflicting mod. Since l is proven,
                    # then all complements of same and any other mod is refuted.
                    self.Refuted(l.complement,r.mod)
                    conflicts = []
                    if r.mod == SI:
                        conflicts = [B, O]
                    elif r.mod == I:
                        conflicts = [B]

                    for cmod in conflicts:
                        if cmod != B:
                            self.Refuted(l.complement(),cmod)
                    # all rules with modality r.mod that have l.complement
                    set1 = findModConsequents(r.mod,l.complement())
                    set1 = set1 - R_infd

                    # if there is an r1 in r_inf that conflicts and
                    # is superior than the  current r, and set1 is a
                    # subset of this conflict r_inf set, then proved.
                    set2 = set()
                    for r1 in list(r_inf):
                        if r1.mod in conflicts:
                            set2.add(r1)
                    if set1.issubset(s2):
                        self.Proved(l,r.mod)

            # end AllRules loop. Update defeasible conclusions.
            self.temp_positive_conclusion -= self.positive_conclusion
            self.temp_negative_conclusion -= self.negative_conclusion
            self.positive_conclusion += self.temp_positive_conclusion
            self.negative_conclusion += self.temp_negative_conclusion
        # end main While()
        return self.positive_conclusion, self.negative_conclusion

    """ end DefeasibleExtension() """