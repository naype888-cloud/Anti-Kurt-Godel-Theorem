import AntiGodelCompleteness

#print axioms Gnomon.closedSystem
#print axioms Gnomon.closedChain
#print axioms Gnomon.Sentence.holds_iff_eval
#print axioms Gnomon.Sentence.complete
#print axioms Gnomon.Sentence.consistent
#print axioms Gnomon.massSq_band

example : Gnomon.Sentence.Holds (.lt 2 5) := by decide
