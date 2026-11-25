-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_fderiv_fderiv_add_8ab3e1d1ce6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:40.386336+00:00
-- url     : https://prove2.me/submissions/1a755909-3dd6-4ea7-96a2-f4a091244383

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartHessHolo

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
open ChartMongeAmpereAffineInvariance
variable {D : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
  [IsScalarTower ℝ ℂ E']
namespace GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
theorem _root_.solution {f₁ f₂ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h₁ : ContDiffAt ℝ 2 f₁ y)
    (h₂ : ContDiffAt ℝ 2 f₂ y) :
    fderiv ℝ (fderiv ℝ fun y' => f₁ y' + f₂ y') y = fderiv ℝ (fderiv ℝ f₁) y + fderiv ℝ (fderiv ℝ f₂) y := by
  have heq : fderiv ℝ (fun y' => f₁ y' + f₂ y') =ᶠ[𝓝 y] fun y' => fderiv ℝ f₁ y' + fderiv ℝ f₂ y' := by
    filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with y' a b
    exact fderiv_add (a.differentiableAt (by norm_num)) (b.differentiableAt (by norm_num))
  have hd₁ : DifferentiableAt ℝ (fderiv ℝ f₁) y :=
    (h₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd₂ : DifferentiableAt ℝ (fderiv ℝ f₂) y :=
    (h₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact ((hd₁.hasFDerivAt.add hd₂.hasFDerivAt).congr_of_eventuallyEq heq).fderiv
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
