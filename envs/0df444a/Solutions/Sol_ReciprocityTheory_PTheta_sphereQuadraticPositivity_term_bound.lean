-- Prove2me | solution 1 for ReciprocityTheory.PTheta.sphereQuadraticPositivity.term_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:20:35.751185+00:00
-- url     : https://prove2.me/submissions/33f3dd1a-c31d-4865-a9af-0c205bba4f00

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_quad_transpose
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_norm_eC
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_im_arg
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_coord_bound

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
theorem _root_.solution (a b : ι → ℝ) (z : ι → ℂ) (A : Matrix ι ι ℂ) (l : ι → ℤ) (c R : ℝ)
    (hc0 : 0 < c) (hR0 : 0 ≤ R) (hR : ∀ i, |(z i).im| ≤ R)
    (hq : ∀ x : ι → ℝ, c * ∑ i, x i ^ 2 ≤ x ⬝ᵥ ((A.map Complex.im + (A.map Complex.im)ᵀ) *ᵥ x)) :
    ‖thetaTerm a b z A l‖ ≤ ∏ i, Real.exp (-((Real.pi * c / 2) / 4) * (l i : ℝ) ^ 2 +
      ((2 * Real.pi * R) ^ 2 / (2 * (Real.pi * c / 2)) + (Real.pi * c / 2) / 2 * a i ^ 2)) := by
  have hβ : 0 < Real.pi * c / 2 := by positivity
  obtain ⟨v, hv⟩ : ∃ v : ι → ℝ, v = fun i => (l i : ℝ) + a i := ⟨_, rfl⟩
  have hnorm : ‖thetaTerm a b z A l‖ = Real.exp (-2 * Real.pi *
      (v ⬝ᵥ (A.map Complex.im *ᵥ v) / 2 + v ⬝ᵥ (fun i => (z i).im))) := by
    unfold thetaTerm
    rw [norm_eC, im_arg, ← hv]
  rw [hnorm, ← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hq2 : c * ∑ i, v i ^ 2 ≤ 2 * (v ⬝ᵥ (A.map Complex.im *ᵥ v)) := by
    have h0 := hq v
    rw [add_mulVec, dotProduct_add, quad_transpose] at h0
    linarith
  have hz : -(v ⬝ᵥ (fun i => (z i).im)) ≤ R * ∑ i, |v i| := by
    rw [Finset.mul_sum, dotProduct, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    show -(v i * (z i).im) ≤ R * |v i|
    have h1 := hR i
    have h2 : -(v i * (z i).im) ≤ |v i| * |(z i).im| := by
      rw [← abs_mul]
      exact neg_le_abs _
    nlinarith [abs_nonneg (v i), mul_le_mul_of_nonneg_left h1 (abs_nonneg (v i))]
  have hcb : ∀ i, -(Real.pi * c / 2) * v i ^ 2 + 2 * Real.pi * R * |v i| ≤
      -((Real.pi * c / 2) / 4) * (l i : ℝ) ^ 2 +
        ((2 * Real.pi * R) ^ 2 / (2 * (Real.pi * c / 2)) + (Real.pi * c / 2) / 2 * a i ^ 2) := by
    intro i
    rw [hv]
    exact coord_bound _ _ _ _ hβ (by positivity)
  calc -2 * Real.pi * (v ⬝ᵥ (A.map Complex.im *ᵥ v) / 2 + v ⬝ᵥ (fun i => (z i).im))
      ≤ ∑ i, (-(Real.pi * c / 2) * v i ^ 2 + 2 * Real.pi * R * |v i|) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        nlinarith [mul_le_mul_of_nonneg_left hq2 Real.pi_pos.le,
          mul_le_mul_of_nonneg_left hz (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    _ ≤ _ := Finset.sum_le_sum fun i _ => hcb i
end ReciprocityTheory.PTheta.sphereQuadraticPositivity
