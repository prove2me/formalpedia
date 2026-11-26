-- Prove2me | solution 1 for Stanley.chromaticPolynomial_eq_external
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:17.112014+00:00
-- url     : https://prove2.me/submissions/cb7cf770-520b-460a-9c97-012c5ed344f2

module
public import Definitions.Def_ChromaticPolynomial_ChromaticPolynomial
public import Definitions.Def_Stanley_SourceSum
public import Mathlib.Algebra.Polynomial.Roots
public import Definitions.Def_Stanley_Convolution

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u v w
variable {V : Type u} {α : Type v} {β : Type w} [Fintype V] (G : SimpleGraph V)
namespace Stanley
theorem _root_.solution : chromaticPolynomial G = G.ChromaticPolynomial ℤ := by
  classical
  rw [chromaticPolynomial, finsum_eq_sum_of_fintype]
  unfold SimpleGraph.ChromaticPolynomial
  apply Finset.sum_congr rfl
  intro F _
  have e : (G.spanningSubgraph_fromEdgeSet' F).coe ≃g fromEdgeSet F.val :=
    { toEquiv := Equiv.Set.univ V, map_rel_iff' := by intros; rfl }
  have hc := Fintype.card_congr e.connectedComponentEquiv
  simp only [Nat.card_eq_fintype_card]
  unfold SimpleGraph.edge_subset_ConnectedComponent_card
  rw [hc]
end Stanley
