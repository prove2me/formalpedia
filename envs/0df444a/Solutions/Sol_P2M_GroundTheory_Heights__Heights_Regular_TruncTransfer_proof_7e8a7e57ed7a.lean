-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_proof_7e8a7e57ed7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:52.957808+00:00
-- url     : https://prove2.me/submissions/a2cd38ce-ae7d-4cc5-8015-36e997ce71ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PTruncTransfer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_pair_b614e5fd0ac9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Set
open ReciprocityTheory.AnForm.A (coordDiv limsupExt polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace TruncTransfer
theorem _root_.solution : TruncTransfer.Statement := by
  intro X _ _ _ D A R
  choose δ₀ hδ₀ c₀ hc₀ L₀ B₀ hP using fun j k => TruncTransfer.pair R j k
  obtain ⟨L', hL'⟩ := (Set.finite_range (fun p : Fin R.N × Fin R.N => L₀ p.1 p.2)).bddAbove
  obtain ⟨B, hB⟩ := (Set.finite_range (fun p : Fin R.N × Fin R.N => B₀ p.1 p.2)).bddAbove
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = max 1 (2 * L') := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := (Set.finite_range
    (fun p : Fin R.N × Fin R.N => max (δ₀ p.1 p.2)⁻¹ (L / c₀ p.1 p.2))).bddAbove
  have hm1 : 0 < max m 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(max m 1)⁻¹, L, B, inv_pos.2 hm1, hL ▸ le_max_left _ _,
    fun K j k x hx t ht htδ y hy => ?_⟩
  have hmj : max (δ₀ j k)⁻¹ (L / c₀ j k) ≤ max m 1 :=
    (hm (Set.mem_range_self (j, k)) : _).trans (le_max_left _ _)
  refine hP j k (max m 1)⁻¹ L B ?_ ?_ ?_ (hL ▸ le_max_left _ _)
    (hB (Set.mem_range_self (j, k))) K x hx t ht htδ y hy
  · exact inv_le_of_inv_le₀ (hδ₀ j k) ((le_max_left _ _).trans hmj)
  · have h1 : L / c₀ j k ≤ max m 1 := (le_max_right _ _).trans hmj
    rw [div_le_iff₀ (hc₀ j k)] at h1
    rw [← div_eq_mul_inv, div_le_iff₀ hm1]
    linarith [mul_comm (max m 1) (c₀ j k)]
  · have h2 : L₀ j k ≤ L' := hL' (Set.mem_range_self (j, k))
    rw [hL]
    exact le_trans (by linarith) (le_max_right _ _)
end TruncTransfer
end GroundTheory.Heights₂.Heights.Regular
