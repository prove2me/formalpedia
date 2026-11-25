-- Prove2me | solution 1 for SimpleGraph.binomialRandom_real_isClique_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:04:11.08113+00:00
-- url     : https://prove2.me/submissions/b7c96f23-dd58-46e7-95c1-911f8a50e413

module
public import Definitions.Def_ProbabilisticMethod_RandomGraph
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Definitions.Def_ProbabilisticMethod_MeasureBridge
public import Theorems.Thm_SimpleGraph_binomialRandom_real_eq_bernoulliProb
public import Theorems.Thm_SimpleGraph_bernoulliProb_isClique_compl
public import Theorems.Thm_SimpleGraph_isClique_compl_fromEdgeSet_iff


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
    G(V, p).real {G | Gᶜ.IsClique (s : Set V)} = (1 - (p : ℝ)) ^ (#s).choose 2 := by
  classical
  have := Fintype.ofFinite V
  exact (binomialRandom_real_eq_bernoulliProb p fun _ _ =>
    isClique_compl_fromEdgeSet_iff.trans disjoint_comm).trans (bernoulliProb_isClique_compl s)
end SimpleGraph
