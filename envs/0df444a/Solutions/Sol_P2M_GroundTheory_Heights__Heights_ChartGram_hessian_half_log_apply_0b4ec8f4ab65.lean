-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartGram_hessian_half_log_apply_0b4ec8f4ab65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:46:03.348585+00:00
-- url     : https://prove2.me/submissions/a97765c1-2627-4a9e-90eb-ce55a0349277

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_hasFDerivAt_re_inner_9db30845c0dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_re_inner_self_pos_4ec83ff2d5a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_re_inner_comm_a8b0e44bf3d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartGram_fderiv_half_log_apply_b1700aa98f9b

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
theorem _root_.solution [CompleteSpace F] {u : E → F} {y : E}
    (hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y') (h0 : u y ≠ 0) (a b : E) :
    fderiv ℝ (fderiv ℝ (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re)) y a b =
      ((⟪u y, fderiv ℂ (fderiv ℂ u) y a b⟫_ℂ).re + (⟪fderiv ℂ u y a, fderiv ℂ u y b⟫_ℂ).re) *
          ((⟪u y, u y⟫_ℂ).re)⁻¹ -
        (⟪u y, fderiv ℂ u y b⟫_ℂ).re * (2 * (⟪u y, fderiv ℂ u y a⟫_ℂ).re) *
          (((⟪u y, u y⟫_ℂ).re) ^ 2)⁻¹ := by
  set ψ : E → ℝ := fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re with hψ
  have hy : AnalyticAt ℂ u y := hu.self_of_nhds
  have hN := ChartGram.re_inner_self_pos h0

  have hc : ContDiffAt ℝ 2 ψ y := by
    have hu2 : ContDiffAt ℝ 2 u y := (hy.contDiffAt (n := 2)).restrict_scalars ℝ
    have hi : ContDiffAt ℝ 2 (fun y' => (⟪u y', u y'⟫_ℂ).re) y :=
      Complex.reCLM.contDiff.contDiffAt.comp y (ContDiffAt.inner ℂ hu2 hu2)
    exact contDiffAt_const.mul (hi.log hN.ne')
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ ψ) y a b = fderiv ℝ (fun y' => fderiv ℝ ψ y' b) y a := by
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  rw [h2]

  have hev : (fun y' => fderiv ℝ ψ y' b) =ᶠ[𝓝 y]
      fun y' => (⟪u y', fderiv ℂ u y' b⟫_ℂ).re * ((⟪u y', u y'⟫_ℂ).re)⁻¹ := by
    filter_upwards [hu, hy.continuousAt.eventually_ne h0] with y' h1 h2
    exact ChartGram.fderiv_half_log_apply h1.differentiableAt h2 b
  rw [hev.fderiv_eq]
  have hu1 : HasFDerivAt u ((fderiv ℂ u y).restrictScalars ℝ) y :=
    hy.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hW : HasFDerivAt (fun y' => fderiv ℂ u y' b)
      (((fderiv ℂ u y).comp (0 : E →L[ℂ] E) + (fderiv ℂ (fderiv ℂ u) y).flip b).restrictScalars ℝ) y :=
    (hy.fderiv.differentiableAt.hasFDerivAt.clm_apply (hasFDerivAt_const b y)).restrictScalars ℝ
  have hI := (hasDerivAt_inv hN.ne').comp_hasFDerivAt y (ChartGram.hasFDerivAt_re_inner hu1 hu1)
  have hg := HasFDerivAt.mul (ChartGram.hasFDerivAt_re_inner hu1 hW) hI
  have hg' : HasFDerivAt (fun y' => (⟪u y', fderiv ℂ u y' b⟫_ℂ).re * ((⟪u y', u y'⟫_ℂ).re)⁻¹) _ y := hg
  rw [hg'.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.coe_restrictScalars', Complex.reCLM_apply, Complex.add_re, smul_eq_mul,
    zero_apply, map_zero, ContinuousLinearMap.flip_apply,
    zero_add, Function.comp_apply]
  rw [ChartGram.re_inner_comm (fderiv ℂ u y a) (u y)]
  ring
end ChartGram
end GroundTheory.Heights₂.Heights
