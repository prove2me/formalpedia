-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereLawFirstCoord_density_Ici_1e097aef9654
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:18:12.460994+00:00
-- url     : https://prove2.me/submissions/c01cf7ca-0a70-4634-960c-5d439b013312

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawFirstCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory ProbabilityTheory Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereLawFirstCoord
open SphereMean
namespace GroundTheory.Heights₂.Heights.SphereLawFirstCoord
theorem _root_.solution (k : ℕ) (c : ℝ) :
    (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal
        (Set.indicator (Set.Icc 0 1) (fun x ↦ (k + 1 : ℝ) * (1 - x) ^ k) x)) (Ici c) =
      ENNReal.ofReal ((1 - min (max c 0) 1) ^ (k + 1)) := by
  rw [withDensity_apply _ measurableSet_Ici]
  have hind : ∀ x : ℝ, ENNReal.ofReal (Set.indicator (Set.Icc 0 1)
      (fun x ↦ (k + 1 : ℝ) * (1 - x) ^ k) x) =
      Set.indicator (Set.Icc 0 1) (fun x ↦ ENNReal.ofReal ((k + 1 : ℝ) * (1 - x) ^ k)) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [hx]
  simp_rw [hind]
  rw [setLIntegral_indicator measurableSet_Icc]
  have hI : Icc (0 : ℝ) 1 ∩ Ici c = Icc (max c 0) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc, max_le_iff]
    tauto
  rw [hI]
  rcases le_or_gt (max c 0) 1 with hd | hd
  · rw [min_eq_left hd, ← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hd,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun x ↦ x ^ k) (1 : ℝ), integral_pow]
      congr 1
      field_simp
      simp
    · exact (by fun_prop : Continuous fun x : ℝ ↦ (k + 1 : ℝ) * (1 - x) ^ k).integrableOn_Icc
    · refine ae_restrict_of_forall_mem measurableSet_Icc fun x hx ↦ ?_
      exact mul_nonneg (by positivity) (pow_nonneg (by linarith [hx.2]) k)
  · rw [Icc_eq_empty (not_le.2 hd), Measure.restrict_empty, lintegral_zero_measure,
      min_eq_right hd.le]
    simp
end GroundTheory.Heights₂.Heights.SphereLawFirstCoord
