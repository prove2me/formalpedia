-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.dens_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:50.158493+00:00
-- url     : https://prove2.me/submissions/3208044e-0842-4b31-9709-512716cb416b

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_DictHaar
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_map_mul_vol
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_measurable_dens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution (s : ι → ℂ) (hs : ∀ w, s w ≠ 0) (A : Set (ι → ℂ)) (hA : MeasurableSet A) :
    volume.withDensity (fun c => (dens c : ℝ≥0∞)) ((fun c => s * c) ⁻¹' A) = volume.withDensity (fun c => (dens c : ℝ≥0∞)) A := by
  have hm : Measurable fun c : ι → ℂ => s * c := by fun_prop
  have hp : 0 < ∏ w, ‖s w‖ ^ 2 := Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hs w)) 2
  have hd : Measurable fun c : ι → ℂ => (dens c : ℝ≥0∞) := measurable_dens.coe_nnreal_ennreal
  rw [withDensity_apply _ (hm hA), withDensity_apply _ hA, ← lintegral_indicator (hm hA), ← lintegral_indicator hA]
  have e : ∀ c, ((fun c => s * c) ⁻¹' A).indicator (fun c => (dens c : ℝ≥0∞)) c =
      ENNReal.ofReal (∏ w, ‖s w‖ ^ 2) * A.indicator (fun c => (dens c : ℝ≥0∞)) (s * c) := by
    intro c
    by_cases h : s * c ∈ A
    · rw [indicator_of_mem (show c ∈ (fun c => s * c) ⁻¹' A from h), indicator_of_mem h, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hp.le]
      congr 1
      change (∏ w, ‖c w‖ ^ 2)⁻¹ = (∏ w, ‖s w‖ ^ 2) * (∏ w, ‖(s * c) w‖ ^ 2)⁻¹
      simp only [Pi.mul_apply, norm_mul, mul_pow, Finset.prod_mul_distrib, mul_inv]
      rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    · rw [indicator_of_notMem (show c ∉ (fun c => s * c) ⁻¹' A from h), indicator_of_notMem h, mul_zero]
  simp only [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_map (hd.indicator hA) hm, map_mul_vol s hs,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hp.le, mul_inv_cancel₀ hp.ne', ENNReal.ofReal_one,
    one_mul]
end PositivityTheory.ThKG.Loc.Bump
