-- Prove2me | solution 1 for Paper.Hypergraph.adw_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:06.244425+00:00
-- url     : https://prove2.me/submissions/24ddd374-72a8-412b-812d-fd17764b8863

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_optimalWidth_bounds
import Theorems.Thm_Paper_Hypergraph_modularWeight_vertex_le_one

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (hH : H.vertices.Nonempty) : 1 ≤ H.adw := by
  obtain ⟨v, hv⟩ := hH
  let w : ℕ → ℝ := fun u => if u = v then 1 else 0
  have hw : H.ModularWeight w := by
    constructor
    · intro u; dsimp [w]; split_ifs <;> norm_num
    · intro e he; simp [w]; split_ifs <;> norm_num
  have hlower : 1 ≤ H.optimalWidth (modularValue w) := by
    unfold optimalWidth
    refine le_csInf ⟨_, 0, H.oneBag, rfl⟩ ?_
    rintro r ⟨n, D, rfl⟩
    obtain ⟨t, ht⟩ := D.vertex_covered v hv
    have hmem : modularValue w (D.bag t) ∈
        Set.range (fun t => modularValue w (D.bag t)) := ⟨t, rfl⟩
    have hle := le_csSup (Set.finite_range _).bddAbove hmem
    simpa [TreeDecomposition.bagWidth, modularValue, w, ht] using hle
  apply hlower.trans
  unfold adw
  refine le_csSup ?_ ⟨w, hw, rfl⟩
  refine ⟨H.vertices.card, ?_⟩
  rintro r ⟨w', hw', rfl⟩
  calc
    H.optimalWidth (modularValue w') ≤ modularValue w' H.vertices :=
      (H.optimalWidth_bounds _ (fun S _ => sum_nonneg (fun u _ => hw'.1 u))).2
    _ ≤ (H.vertices.card : ℝ) := by
      simpa [modularValue] using
        (sum_le_sum (fun u hu => H.modularWeight_vertex_le_one hw' hu))
end Paper.Hypergraph
