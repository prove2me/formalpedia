-- Prove2me | solution 1 for SimpleGraph.binomialRandom_real_isClique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:04:09.057281+00:00
-- url     : https://prove2.me/submissions/5de4c4a4-6ce5-4fad-a938-b082d9048fa4

module
public import Definitions.Def_ProbabilisticMethod_RandomGraph
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Definitions.Def_ProbabilisticMethod_MeasureBridge
public import Theorems.Thm_SimpleGraph_binomialRandom_real_eq_bernoulliProb
public import Theorems.Thm_SimpleGraph_bernoulliProb_isClique
public import Theorems.Thm_SimpleGraph_isClique_fromEdgeSet_iff


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory unitInterval
open scoped Finset
open SimpleGraph
variable {V : Type*}
variable [Finite V]
namespace SimpleGraph
theorem _root_.solution (p : I) (s : Finset V) :
    G(V, p).real {G | G.IsClique (s : Set V)} = (p : ℝ) ^ (#s).choose 2 := by
  classical
  have := Fintype.ofFinite V
  exact (binomialRandom_real_eq_bernoulliProb p fun _ _ => isClique_fromEdgeSet_iff).trans
    (bernoulliProb_isClique s)
end SimpleGraph
