-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_cuspTime_hasFDerivAt_570f460d4fba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:48.872813+00:00
-- url     : https://prove2.me/submissions/1c6eaaf4-ec9c-412d-8226-c1bd7376c062

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PHodgeDerivative
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_logNorm_hasFDerivAt_5a4ea0d5a7ec

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
open Metric Filter Topology Matrix
open GroundTheory.Heights₂.Heights.MCBounds GroundTheory.Heights₂.Heights.MCDet
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
namespace GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
theorem _root_.solution {n a : ℕ} (h : a ≤ n) (i : Fin a) {z : Fin n → ℂ}
    (hz : cuspCoord h z i ≠ 0) :
    ∃ L : (Fin n → ℂ) →L[ℝ] ℝ, HasFDerivAt (fun y => cuspTime h y i) L z ∧
      ‖L‖ ≤ ‖cuspCoord h z i‖⁻¹ := by
  obtain ⟨L, hL, hLn⟩ := logNorm_hasFDerivAt hz
  have hp : HasFDerivAt (fun y : Fin n → ℂ => y (Fin.castLE h i))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) (Fin.castLE h i)) z :=
    hasFDerivAt_apply _ _
  have h2 := (hL.comp z hp).const_mul (-(2 * Real.pi)⁻¹)
  have e : (fun y : Fin n → ℂ => -(2 * Real.pi)⁻¹ * (Real.log ‖y (Fin.castLE h i)‖)) =
      fun y => cuspTime h y i := by
    funext y
    simp only [cuspTime, cuspCoord, Real.log_inv]
    ring
  rw [Function.comp_def, e] at h2
  refine ⟨_, h2, ?_⟩
  have hproj : ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) (Fin.castLE h i)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      simpa using norm_le_pi_norm v (Fin.castLE h i)
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hc : ‖(-(2 * Real.pi)⁻¹ : ℝ)‖ ≤ 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ hpi
  calc ‖(-(2 * Real.pi)⁻¹ : ℝ) • L.comp _‖
      ≤ ‖(-(2 * Real.pi)⁻¹ : ℝ)‖ * (‖L‖ * 1) := by
        rw [norm_smul]
        gcongr
        exact (L.opNorm_comp_le _).trans (by gcongr)
    _ ≤ 1 * (‖cuspCoord h z i‖⁻¹ * 1) := by gcongr
    _ = ‖cuspCoord h z i‖⁻¹ := by ring
end GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
