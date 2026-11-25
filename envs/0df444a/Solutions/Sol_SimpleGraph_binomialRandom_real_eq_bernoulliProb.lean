-- Prove2me | solution 1 for SimpleGraph.binomialRandom_real_eq_bernoulliProb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:14.415333+00:00
-- url     : https://prove2.me/submissions/3be6f737-03b0-47df-881f-b585bcdec6a9

module
public import Definitions.Def_ProbabilisticMethod_RandomGraph
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Definitions.Def_ProbabilisticMethod_MeasureBridge
public import Theorems.Thm_Finset_setBernoulli_real_eq_bernoulliProb
public import Theorems.Thm_SimpleGraph_coe_possibleEdges

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory unitInterval
open scoped Finset
open SimpleGraph
variable {V : Type*}
variable [Fintype V] [DecidableEq V]
namespace SimpleGraph
theorem _root_.solution (p : I) {S : Set (SimpleGraph V)}
    {Q : Finset (Sym2 V) → Prop} [DecidablePred Q]
    (hQ : ∀ A ⊆ possibleEdges V, fromEdgeSet (A : Set (Sym2 V)) ∈ S ↔ Q A) :
    G(V, p).real S = (possibleEdges V).bernoulliProb p Q := by
  rw [measureReal_def, binomialRandom_apply', ← measureReal_def, ← coe_possibleEdges]
  refine Finset.setBernoulli_real_eq_bernoulliProb _ p fun A hA =>
    ⟨fun ⟨G, hG, hGA⟩ => (hQ A hA).mp ?_, fun h => ⟨_, (hQ A hA).mpr h, ?_⟩⟩
  · rwa [← hGA, fromEdgeSet_edgeSet]
  · ext e
    have : e ∈ (A : Set (Sym2 V)) → ¬e.IsDiag := fun he => by
      simpa [Sym2.diagSet] using (coe_possibleEdges (V := V)).subset (hA he)
    rw [edgeSet_fromEdgeSet]
    exact ⟨And.left, fun he => ⟨he, by simpa [Sym2.diagSet] using this he⟩⟩
end SimpleGraph
