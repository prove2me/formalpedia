-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartGram_fderiv_half_log_apply_b1700aa98f9b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:31.988494+00:00
-- url     : https://prove2.me/submissions/84f8ba52-4006-4c47-b424-5402cc444216

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_hasFDerivAt_re_inner_9db30845c0dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_re_inner_self_pos_4ec83ff2d5a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_re_inner_comm_a8b0e44bf3d7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open scoped InnerProductSpace
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
namespace GroundTheory.Heights₂.Heights
namespace ChartGram
theorem _root_.solution {u : E → F} {y : E}
    (hu : DifferentiableAt ℂ u y) (h0 : u y ≠ 0) (b : E) :
    fderiv ℝ (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y b =
      (⟪u y, fderiv ℂ u y b⟫_ℂ).re * ((⟪u y, u y⟫_ℂ).re)⁻¹ := by
  have h1 : HasFDerivAt u ((fderiv ℂ u y).restrictScalars ℝ) y := hu.hasFDerivAt.restrictScalars ℝ
  have h4 := HasFDerivAt.const_mul (HasFDerivAt.log (ChartGram.hasFDerivAt_re_inner h1 h1)
    (ChartGram.re_inner_self_pos h0).ne') 2⁻¹
  rw [h4.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, ContinuousLinearMap.coe_restrictScalars',
    Complex.reCLM_apply, Complex.add_re, smul_eq_mul]
  rw [ChartGram.re_inner_comm (fderiv ℂ u y b)]
  ring
end ChartGram
end GroundTheory.Heights₂.Heights
