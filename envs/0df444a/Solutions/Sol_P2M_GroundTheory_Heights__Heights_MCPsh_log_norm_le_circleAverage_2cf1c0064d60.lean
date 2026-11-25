-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_log_norm_le_circleAverage_2cf1c0064d60
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:20.204253+00:00
-- url     : https://prove2.me/submissions/e39b4378-7cf0-4baa-9585-e56acb16c22b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore

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
open Metric Filter Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCPsh
theorem _root_.solution {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1))
    (h0 : h 0 ≠ 0) :
    Real.log ‖h 0‖ ≤ circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 := by
  have hh' : AnalyticOnNhd ℂ h (closedBall 0 |(1 : ℝ)|) := by simpa using hh
  rw [hh'.circleAverage_log_norm one_ne_zero h0]
  have hnn : ∀ u : ℂ, 0 ≤ (MeromorphicOn.divisor h (closedBall 0 |(1:ℝ)|) u : ℝ) *
      Real.log (1 * ‖(0:ℂ) - u‖⁻¹) := by
    intro u
    by_cases hu : u ∈ closedBall (0:ℂ) |(1:ℝ)|
    · refine mul_nonneg ?_ ?_
      · exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hh') u
      · rw [one_mul, zero_sub, norm_neg]
        rcases eq_or_ne u 0 with rfl | hu0
        · simp
        · apply Real.log_nonneg
          have h1 : ‖u‖ ≤ 1 := by simpa using hu
          have h2 : 0 < ‖u‖ := norm_pos_iff.mpr hu0
          rw [le_inv_comm₀ zero_lt_one h2]
          simpa using h1
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      simp
  linarith [finsum_nonneg hnn]
end GroundTheory.Heights₂.Heights.MCPsh
