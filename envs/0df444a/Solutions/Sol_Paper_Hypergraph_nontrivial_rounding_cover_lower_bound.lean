-- Prove2me | solution 1 for Paper.Hypergraph.nontrivial_rounding_cover_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:50.518409+00:00
-- url     : https://prove2.me/submissions/b744c5aa-6525-42e7-aa92-cda07553ce42

import Definitions.Def_Paper_RoundingRecursion
import Definitions.Def_Paper_TwoTerminalRounding
import Definitions.Def_Paper_BalancedRounding
import Theorems.Thm_Paper_Hypergraph_rounding_volume_factor_le
import Theorems.Thm_Paper_Hypergraph_component_mem_iff_reachable
import Theorems.Thm_Paper_Hypergraph_edgeVolume_mono
import Theorems.Thm_Paper_Hypergraph_induced_vertexDistance_le_two_coverCost
import Theorems.Thm_Paper_Hypergraph_roundingBall_volume_le


set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) {γ x : ℕ → ℝ} {φ : ℝ}
    (hφ : 0 < φ ∧ φ < 1) (hγ : ∀ e ∈ H.edges, 0 ≤ γ e)
    (hx : H.FractionalBalanced γ φ x)
    (hnontrivial : ¬ H.IntegralBalanced γ ((1 + 3 * φ) / (2 + 2 * φ)) ∅) :
    (1 - φ) / 4 ≤ H.coverCost x := by
  by_contra h
  have hsmall : H.coverCost x < (1 - φ) / 4 := lt_of_not_ge h
  apply hnontrivial
  refine ⟨empty_subset _, ?_⟩
  intro K hK
  simp only [sdiff_empty] at hK
  have hKV := mem_powerset.mp (mem_filter.mp hK).1
  obtain ⟨c, hcK, _⟩ := (mem_filter.mp hK).2
  have hc := hKV hcK
  have hKB : K ⊆ H.roundingBall x H.vertices c ((1 - φ) / 2) := by
    intro v hv
    apply mem_filter.mpr ⟨hKV hv, ?_⟩
    have hcv := ((H.induce H.vertices).component_mem_iff_reachable hK hcK (hKV hv)).mp hv
    have hd := H.induced_vertexDistance_le_two_coverCost (fun z hz => (hx.1 z hz).1)
      H.vertices hc hcv
    linarith
  have hb := H.roundingBall_volume_le hγ hx H.vertices hc
    (show (1 - φ) / 2 < 1 by linarith)
  change H.edgeVolume γ K ≤ _
  exact ((H.edgeVolume_mono hγ hKB).trans hb).trans
    (mul_le_mul_of_nonneg_right (rounding_volume_factor_le hφ) (sum_nonneg hγ))
end Paper.Hypergraph
