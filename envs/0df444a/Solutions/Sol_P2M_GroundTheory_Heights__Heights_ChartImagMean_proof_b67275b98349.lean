-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartImagMean_proof_b67275b98349
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:54:12.43702+00:00
-- url     : https://prove2.me/submissions/063725f4-7d89-4140-af2c-e4467aeb86f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartImagMean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_im_of_analytic_28853a1159d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_log_norm_of_ne_zero_7323d50ed254


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
open Metric Real
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ChartImagMean
theorem _root_.solution : ChartImagMean.Statement := by
  intro D z w hdisc j k
  have hball : ∀ ζ ∈ closedBall (0 : ℂ) 1, z + ζ • w ∈ D.Ustar := fun ζ hζ =>
    hdisc ζ (mem_closedBall_zero_iff.mp hζ)

  have hY : ∀ x, D.Y x j k = (D.τ0 x j k).im +
      ∑ i, (-(2 * π)⁻¹ * D.B i j k) * Real.log ‖x (Fin.castLE D.a_le i)‖ := by
    intro x
    simp only [PeriodChartData.Y, chartImag, Matrix.add_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.map_apply, cuspTime, cuspCoord, smul_eq_mul, Real.log_inv]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

  have hτ : AnalyticOnNhd ℂ (fun ζ : ℂ => D.τ0 (z + ζ • w) j k) (closedBall 0 1) := by
    intro ζ hζ
    exact AnalyticAt.comp (g := fun x => D.τ0 x j k) (f := fun ζ : ℂ => z + ζ • w)
      (D.τ0_analytic j k _ (hball ζ hζ).1)
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  have hc : ∀ i, AnalyticOnNhd ℂ
      (fun ζ : ℂ => z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)) (closedBall 0 1) :=
    fun i ζ _ => analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hcne : ∀ i, ∀ ζ ∈ closedBall (0 : ℂ) 1,
      z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i) ≠ 0 := by
    intro i ζ hζ
    have := (hball ζ hζ).2 i
    simpa [cuspCoord] using this

  have hτc : ContinuousOn (fun ζ : ℂ => (D.τ0 (z + ζ • w) j k).im) (closedBall 0 1) :=
    Complex.continuous_im.comp_continuousOn hτ.continuousOn
  have hlc : ∀ i, ContinuousOn
      (fun ζ : ℂ => (-(2 * π)⁻¹ * D.B i j k) *
        Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖) (closedBall 0 1) := by
    intro i
    refine continuousOn_const.mul ((hc i).continuousOn.norm.log fun ζ hζ => ?_)
    exact norm_ne_zero_iff.mpr (hcne i ζ hζ)
  have hint : ∀ {f : ℂ → ℝ}, ContinuousOn f (closedBall 0 1) → CircleIntegrable f 0 1 :=
    fun hf => (hf.mono sphere_subset_closedBall).circleIntegrable zero_le_one
  have hfun : (fun ζ : ℂ => D.Y (z + ζ • w) j k) = fun ζ : ℂ =>
      (D.τ0 (z + ζ • w) j k).im + ∑ i, (-(2 * π)⁻¹ * D.B i j k) *
        Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖ := by
    funext ζ
    rw [hY]
    simp
  rw [hfun, circleAverage_fun_add (hint hτc)
    (hint (continuousOn_finsetSum _ fun i _ => hlc i)),
    circleAverage_fun_sum fun i _ => hint (hlc i), MCPsh.circleAverage_im_of_analytic hτ, hY z]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hs : circleAverage (fun ζ : ℂ => (-(2 * π)⁻¹ * D.B i j k) *
        Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖) 0 1 =
        (-(2 * π)⁻¹ * D.B i j k) * circleAverage (fun ζ : ℂ =>
        Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖) 0 1 :=
      circleAverage_fun_smul (E := ℝ) (𝕜 := ℝ) (a := -(2 * π)⁻¹ * D.B i j k)
        (f := fun ζ : ℂ => Real.log ‖z (Fin.castLE D.a_le i) + ζ * w (Fin.castLE D.a_le i)‖)
    rw [hs, MCPsh.circleAverage_log_norm_of_ne_zero (hc i) (hcne i)]
    simp
end ChartImagMean
end GroundTheory.Heights₂.Heights
