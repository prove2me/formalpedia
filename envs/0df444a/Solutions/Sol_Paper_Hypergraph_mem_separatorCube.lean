-- Prove2me | solution 1 for Paper.Hypergraph.mem_separatorCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:55.170806+00:00
-- url     : https://prove2.me/submissions/98617a4f-4dfb-4ba1-89cc-98cf691e10f6

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_edgeDistance_eq_finite

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ x : ℕ → ℝ} {θ : ℝ}
    (hx : x ∈ Set.Icc (0 : ℕ → ℝ) 1) :
    x ∈ H.separatorCube γ θ ↔ H.FractionalBalanced γ θ x := by
  have hn : ∀ v ∈ H.vertices, 0 ≤ x v := fun v _ => hx.1 v
  have heq (e : ℕ) (he : e ∈ H.edges) :
      (∑ f ∈ H.edges, γ f * H.edgeDistance x e f) =
        ∑ f ∈ H.edges, γ f * H.finiteEdgeDistance e f x := by
    apply sum_congr rfl
    intro f hf
    rw [H.edgeDistance_eq_finite hn he hf]
  constructor
  · intro h
    exact ⟨fun v _ => ⟨hx.1 v, hx.2 v⟩, fun e he => (heq e he).symm ▸ h.2 e he⟩
  · intro h
    exact ⟨hx, fun e he => heq e he ▸ h.2 e he⟩
end Paper.Hypergraph
