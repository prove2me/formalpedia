-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_HodgeDerivative_logNorm_hasFDerivAt_5a4ea0d5a7ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:59.632464+00:00
-- url     : https://prove2.me/submissions/b95a9090-90e0-4fe5-9ab5-4f1e0959dd62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PHodgeDerivative

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
theorem _root_.solution {x : ℂ} (hx : x ≠ 0) :
    ∃ L : ℂ →L[ℝ] ℝ, HasFDerivAt (fun y : ℂ => Real.log ‖y‖) L x ∧ ‖L‖ ≤ ‖x‖⁻¹ := by
  have hx2 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have h1 := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.log hx2).const_mul (2⁻¹ : ℝ)
  have e : (fun y : ℂ => 2⁻¹ * Real.log (‖y‖ ^ 2)) = fun y : ℂ => Real.log ‖y‖ := by
    funext y
    rw [Real.log_pow]
    push_cast
    ring
  rw [e] at h1
  refine ⟨_, h1, ?_⟩
  rw [two_nsmul, ← two_smul ℝ]
  rw [norm_smul, norm_smul, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), abs_of_pos (by norm_num : (0:ℝ) < 2),
    abs_of_pos (inv_pos.mpr (by positivity))]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply le_of_eq
  field_simp
end GroundTheory.Heights₂.Heights.Regular.HodgeDerivative
