-- Prove2me | solution 1 for Paper.Hypergraph.separator_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:03.640155+00:00
-- url     : https://prove2.me/submissions/9c815608-0240-4729-8ee2-1f5d40432982

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_edgeDistance_eq_finite
import Theorems.Thm_Paper_Hypergraph_finiteEdgeDistance_congr

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ x : ℕ → ℝ} {θ : ℝ}
    (hx : H.FractionalBalanced γ θ x) :
    (fun v => if v ∈ H.vertices then x v else 0) ∈ H.separatorCube γ θ := by
  let y : ℕ → ℝ := fun v => if v ∈ H.vertices then x v else 0
  have hy : y ∈ Set.Icc (0 : ℕ → ℝ) 1 := by
    constructor <;> intro v <;> dsimp [y] <;> split_ifs with hv
    · exact (hx.1 v hv).1
    · norm_num
    · exact (hx.1 v hv).2
    · norm_num
  refine ⟨hy, ?_⟩
  intro e he
  have heq : (∑ f ∈ H.edges, γ f * H.finiteEdgeDistance e f y) =
      ∑ f ∈ H.edges, γ f * H.edgeDistance x e f := by
    apply sum_congr rfl
    intro f hf
    rw [H.edgeDistance_eq_finite (fun v hv => (hx.1 v hv).1) he hf,
      H.finiteEdgeDistance_congr e f (x := y) (y := x) (by intro v hv; simp [y, hv])]
  exact heq.symm ▸ hx.2 e he
end Paper.Hypergraph
