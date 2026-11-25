-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_sub_8677133a77df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:48:47.152863+00:00
-- url     : https://prove2.me/submissions/37b386c0-b572-4b2f-8b31-6cfb9ad3a048

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_kernel_66dd3acd1271

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution (e : ℕ) {f₁ f₂ : ℝ → ℝ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (c₁ c₂ t : ℝ) :
    radialTransform (e + 1) (fun τ => c₁ * f₁ τ - c₂ * f₂ τ) t =
      c₁ * radialTransform (e + 1) f₁ t - c₂ * radialTransform (e + 1) f₂ t := by
  unfold radialTransform
  beta_reduce
  have e1 : ∀ τ : ℝ, (c₁ * f₁ τ - c₂ * f₂ τ) * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1)) =
      c₁ * (f₁ τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))) -
        c₂ * (f₂ τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))) := fun τ => by ring
  simp only [e1]
  rw [intervalIntegral.integral_sub (f := fun τ => c₁ * (f₁ τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))))
      (g := fun τ => c₂ * (f₂ τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))))
      ((continuous_const.mul (h₁.mul (continuous_kernel e))).intervalIntegrable _ _)
      ((continuous_const.mul (h₂.mul (continuous_kernel e))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
