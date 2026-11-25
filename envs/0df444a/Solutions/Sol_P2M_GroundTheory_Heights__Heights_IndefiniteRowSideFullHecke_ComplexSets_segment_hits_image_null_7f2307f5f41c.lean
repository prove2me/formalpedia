-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_segment_hits_image_null_7f2307f5f41c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:09:54.052965+00:00
-- url     : https://prove2.me/submissions/9ac3c8f4-649e-4573-ba89-4f202ce1350a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHausdorffNullComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHausdorffNullComplementConnected
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_radial_lipschitzOnWith_d33722627b5b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Metric MeasureTheory Set Relation
open scoped NNReal ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] {C : Set E} {x : E} (hx : x ∉ C) (ℓ : E →L[ℝ] ℝ) {α : ℝ}
    (hα : α ≠ ℓ x) (g : E →L[ℝ] F) {d : ℝ} (hd : 0 ≤ d) (hC : μH[d] C = 0) :
    μH[d] (g '' {m | ℓ m = α ∧ (segment ℝ x m ∩ C).Nonempty}) = 0 := by
  have hβ : α - ℓ x ≠ 0 := sub_ne_zero.2 hα
  have hsub : g '' {m | ℓ m = α ∧ (segment ℝ x m ∩ C).Nonempty} ⊆
      ⋃ j : ℕ, (g ∘ fun c => x + ((ℓ c - ℓ x) / (α - ℓ x))⁻¹ • (c - x)) ''
        (C ∩ {c | ((j : ℝ) + 1)⁻¹ ≤ (ℓ c - ℓ x) / (α - ℓ x) ∧ ‖c - x‖ ≤ (j : ℝ) + 1}) := by
    rintro _ ⟨m, ⟨hm, c, hcs, hcC⟩, rfl⟩
    rw [segment_eq_image'] at hcs
    obtain ⟨s, ⟨hs0, -⟩, rfl⟩ := hcs
    have hs : s ≠ 0 := by
      rintro rfl
      simp only [zero_smul, add_zero] at hcC
      exact hx hcC
    have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hτ : (ℓ (x + s • (m - x)) - ℓ x) / (α - ℓ x) = s := by
      rw [map_add, map_smul, map_sub, hm, smul_eq_mul, add_sub_cancel_left, mul_div_assoc,
        div_self hβ, mul_one]
    obtain ⟨j, hj⟩ := exists_nat_gt (max s⁻¹ ‖s • (m - x)‖)
    refine mem_iUnion.2 ⟨j, x + s • (m - x), ⟨hcC, ?_, ?_⟩, ?_⟩
    · rw [hτ]
      have h1 : s⁻¹ < (j : ℝ) + 1 := by linarith [le_max_left s⁻¹ ‖s • (m - x)‖]
      calc ((j : ℝ) + 1)⁻¹ ≤ (s⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hspos) h1.le
        _ = s := inv_inv s
    · rw [add_sub_cancel_left]
      linarith [le_max_right s⁻¹ ‖s • (m - x)‖]
    · simp only [Function.comp_apply, hτ, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs,
        one_smul, add_sub_cancel]
  refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
  obtain ⟨K, hK⟩ := radial_lipschitzOnWith x ℓ (β := α - ℓ x) (R := (j : ℝ) + 1)
    (show (0 : ℝ) < ((j : ℝ) + 1)⁻¹ by positivity)
  have hL := g.lipschitz.comp_lipschitzOnWith (hK.mono (inter_subset_right (s := C)))
  refine le_antisymm ?_ zero_le
  calc _ ≤ _ := hL.hausdorffMeasure_image_le hd
    _ = 0 := by rw [measure_mono_null inter_subset_left hC, mul_zero]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
