-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_log_norm_of_ne_zero_7323d50ed254
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:33.650336+00:00
-- url     : https://prove2.me/submissions/8c4d50b3-287c-477e-a336-afb7b1fe85cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPsh
open Metric Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCPsh
theorem _root_.solution {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (hne : ∀ ζ ∈ closedBall (0:ℂ) 1, h ζ ≠ 0) :
    circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 = Real.log ‖h 0‖ := by
  have hh' : AnalyticOnNhd ℂ h (closedBall 0 |(1 : ℝ)|) := by simpa using hh
  rw [hh'.circleAverage_log_norm one_ne_zero (hne 0 (mem_closedBall_self zero_le_one))]
  have hzero : ∀ u : ℂ, (MeromorphicOn.divisor h (closedBall 0 |(1:ℝ)|) u : ℝ) *
      Real.log (1 * ‖(0:ℂ) - u‖⁻¹) = 0 := by
    intro u
    by_cases hu : u ∈ closedBall (0:ℂ) |(1:ℝ)|
    · have hu' : u ∈ closedBall (0:ℂ) 1 := by simpa using hu
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hh' hu, (hh' u hu).analyticOrderAt_eq_zero.mpr (hne u hu')]
      simp
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      simp
  have hz2 : ∀ u : ℂ, -((MeromorphicOn.divisor h (closedBall 0 |(1:ℝ)|) u : ℝ) * Real.log ‖u‖) = 0 := by
    intro u
    have := hzero u
    simp only [one_mul, zero_sub, norm_neg, Real.log_inv, mul_neg] at this
    linarith
  simp only [one_mul, zero_sub, norm_neg, Real.log_inv, mul_neg, hz2, finsum_zero, zero_add]
end GroundTheory.Heights₂.Heights.MCPsh
