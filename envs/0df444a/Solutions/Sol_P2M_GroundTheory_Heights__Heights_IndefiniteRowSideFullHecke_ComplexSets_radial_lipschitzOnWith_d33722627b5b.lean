-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_radial_lipschitzOnWith_d33722627b5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:13.508333+00:00
-- url     : https://prove2.me/submissions/8f580d51-ec9c-4591-9eeb-4e1c51c4b859

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHausdorffNullComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHausdorffNullComplementConnected

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (x : E) (ℓ : E →L[ℝ] ℝ) {β δ : ℝ} (hδ : 0 < δ) (R : ℝ) :
    ∃ K, LipschitzOnWith K (fun c => x + ((ℓ c - ℓ x) / β)⁻¹ • (c - x))
      {c | δ ≤ (ℓ c - ℓ x) / β ∧ ‖c - x‖ ≤ R} := by
  refine ⟨_, LipschitzOnWith.of_dist_le' (K := δ⁻¹ + ‖ℓ‖ * R / (|β| * (δ * δ))) ?_⟩
  rintro a ⟨ha, -⟩ b ⟨hb, hbR⟩
  set ta := (ℓ a - ℓ x) / β with hta_def
  set tb := (ℓ b - ℓ x) / β with htb_def
  have hta : 0 < ta := hδ.trans_le ha
  have htb : 0 < tb := hδ.trans_le hb
  have hβ : β ≠ 0 := by
    rintro rfl
    rw [hta_def, div_zero] at hta
    exact lt_irrefl _ hta
  have hkey : x + ta⁻¹ • (a - x) - (x + tb⁻¹ • (b - x)) =
      ta⁻¹ • (a - b) + (ta⁻¹ - tb⁻¹) • (b - x) := by
    simp only [smul_sub, sub_smul]; abel
  have hdiff : tb - ta = ℓ (b - a) / β := by
    rw [hta_def, htb_def, map_sub]; ring
  have hinv : |ta⁻¹ - tb⁻¹| ≤ ‖ℓ‖ * ‖a - b‖ / (|β| * (δ * δ)) := by
    rw [inv_sub_inv hta.ne' htb.ne', hdiff, abs_div, abs_div, abs_of_pos (mul_pos hta htb), div_div]
    apply div_le_div₀ (by positivity)
    · rw [← Real.norm_eq_abs, norm_sub_rev a b]
      exact ℓ.le_opNorm _
    · exact mul_pos (abs_pos.2 hβ) (mul_pos hδ hδ)
    · exact mul_le_mul_of_nonneg_left (mul_le_mul ha hb hδ.le hta.le) (abs_nonneg _)
  rw [dist_eq_norm, dist_eq_norm, hkey]
  calc ‖ta⁻¹ • (a - b) + (ta⁻¹ - tb⁻¹) • (b - x)‖
      ≤ ‖ta⁻¹ • (a - b)‖ + ‖(ta⁻¹ - tb⁻¹) • (b - x)‖ := norm_add_le _ _
    _ = ta⁻¹ * ‖a - b‖ + |ta⁻¹ - tb⁻¹| * ‖b - x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hta)]
    _ ≤ δ⁻¹ * ‖a - b‖ + ‖ℓ‖ * ‖a - b‖ / (|β| * (δ * δ)) * R := by
        gcongr
    _ = (δ⁻¹ + ‖ℓ‖ * R / (|β| * (δ * δ))) * ‖a - b‖ := by ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
