-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_mul_8992812ba236
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:39.562806+00:00
-- url     : https://prove2.me/submissions/6a166509-b885-426e-9c35-7301c319bbb4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaIntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PDeltaIntSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries Filter Topology Finset
open scoped Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
theorem _root_.solution {F G : PowerSeries ℤ} {r : ℝ} (hr : 0 ≤ r) (hF : IntSeriesConv F r)
    (hG : IntSeriesConv G r) : IntSeriesConv (F * G) r := by
  have hF' : Summable fun n ↦ ‖|((coeff n F : ℤ) : ℝ)| * r ^ n‖ := by
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_pow, abs_of_nonneg hr]; exact hF
  have hG' : Summable fun n ↦ ‖|((coeff n G : ℤ) : ℝ)| * r ^ n‖ := by
    simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_pow, abs_of_nonneg hr]; exact hG
  refine (summable_norm_sum_mul_antidiagonal_of_summable_norm hF' hG').of_nonneg_of_le
    (fun n ↦ mul_nonneg (abs_nonneg _) (pow_nonneg hr _)) fun n ↦ ?_
  rw [coeff_mul, Int.cast_sum, Real.norm_eq_abs]
  refine ((mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) (pow_nonneg hr _)).trans_eq ?_).trans
    (le_abs_self _)
  rw [sum_mul]
  refine sum_congr rfl fun ij hij ↦ ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  rw [← hij, pow_add, Int.cast_mul, abs_mul]
  ring
end GroundTheory.Heights₂.Heights.ChowlaSelberg
