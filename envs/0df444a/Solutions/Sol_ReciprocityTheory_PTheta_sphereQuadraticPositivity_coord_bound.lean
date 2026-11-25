-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.coord_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:37:40.113264+00:00
-- url     : https://prove2.me/submissions/a9589d70-d4aa-4d05-9c14-623d332abbec

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta.sphereQuadraticPositivity
theorem _root_.solution (β γ k a : ℝ) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    -β * (k + a) ^ 2 + γ * |k + a| ≤ -(β / 4) * k ^ 2 + (γ ^ 2 / (2 * β) + β / 2 * a ^ 2) := by
  have hβ' : β ≠ 0 := hβ.ne'
  have h1 : γ * |k + a| ≤ β / 2 * |k + a| ^ 2 + γ ^ 2 / (2 * β) := by
    have e : β / 2 * |k + a| ^ 2 + γ ^ 2 / (2 * β) - γ * |k + a| =
        (β * |k + a| - γ) ^ 2 / (2 * β) := by
      field_simp
      ring
    have h0 : 0 ≤ (β * |k + a| - γ) ^ 2 / (2 * β) := by positivity
    linarith
  rw [sq_abs] at h1
  have h2 : k ^ 2 ≤ 2 * (k + a) ^ 2 + 2 * a ^ 2 := by nlinarith [sq_nonneg (k + 2 * a)]
  have h3 := mul_le_mul_of_nonneg_left h2 hβ.le
  nlinarith [h1, h3]
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
