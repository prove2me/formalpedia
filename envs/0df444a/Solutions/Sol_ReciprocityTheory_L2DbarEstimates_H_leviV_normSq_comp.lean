-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.leviV_normSq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:20.812151+00:00
-- url     : https://prove2.me/submissions/9a9bcdbf-c92f-4b33-ad49-06bbf25e22e8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_ofReal_normSq_sum_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex ComplexConjugate Filter Topology Matrix
namespace ReciprocityTheory.L2DbarEstimates.H
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
private theorem wd_apply_congr_of_eventuallyEq {j : Fin n} {f g : V n → ℂ} {x : V n} (h : f =ᶠ[𝓝 x] g) :
    wd n j f x = wd n j g x := by
  unfold wd
  rw [h.fderiv_eq]
private theorem wd_eq_fderiv_basis_of_differentiableAt {j : Fin n} {g : V n → ℂ} {y : V n} (hy : DifferentiableAt ℂ g y) :
    wd n j g y = fderiv ℝ g y (bas n j) := by
  have hlin : fderiv ℝ g y (Complex.I • bas n j) = Complex.I * fderiv ℝ g y (bas n j) := by
    rw [hy.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  unfold wd
  rw [hlin]
  linear_combination (-(fderiv ℝ g y (bas n j)) / 2) * Complex.I_mul_I
private theorem wdb_normSq_eq_mul_conj_wd {k : Fin n} {g : V n → ℂ} {y : V n} (hy : DifferentiableAt ℂ g y) :
    wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) y = g y * conj (wd n k g y) := by
  have hD : HasFDerivAt g (fderiv ℝ g y) y := (hy.restrictScalars ℝ).hasFDerivAt
  have hlin : ∀ v : V n, fderiv ℝ g y (Complex.I • v) = Complex.I * fderiv ℝ g y v := by
    intro v
    rw [hy.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hc : HasFDerivAt (fun y => conj (g y))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g y)) y :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp y hD
  have hh : HasFDerivAt (fun y => g y * conj (g y))
      (g y • (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g y) + conj (g y) • fderiv ℝ g y) y :=
    hD.mul hc
  have hfun : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) := by
    funext y
    exact (Complex.mul_conj (g y)).symm
  rw [wd_eq_fderiv_basis_of_differentiableAt hy]
  unfold wdb
  rw [hfun, hh.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, hlin, map_mul, Complex.conj_I]
  linear_combination ((conj (g y) * fderiv ℝ g y (bas n k) -
    g y * conj (fderiv ℝ g y (bas n k))) / 2) * Complex.I_mul_I
private theorem wd_mul_conj_of_differentiableAt {j : Fin n} {g h : V n → ℂ} {x : V n}
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℂ h x) :
    wd n j (fun y => g y * conj (h y)) x = wd n j g x * conj (h x) := by
  have hD : HasFDerivAt g (fderiv ℝ g x) x := hg.hasFDerivAt
  have hH : HasFDerivAt h (fderiv ℝ h x) x := (hh.restrictScalars ℝ).hasFDerivAt
  have hlin : ∀ v : V n, fderiv ℝ h x (Complex.I • v) = Complex.I * fderiv ℝ h x v := by
    intro v
    rw [hh.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  have hc : HasFDerivAt (fun y => conj (h y))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ h x)) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x hH
  have hp : HasFDerivAt (fun y => g y * conj (h y))
      (g x • (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ h x) + conj (h x) • fderiv ℝ g x) x :=
    hD.mul hc
  unfold wd
  rw [hp.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul, hlin, map_mul, Complex.conj_I]
  linear_combination (g x * conj (fderiv ℝ h x (bas n j)) / 2) * Complex.I_mul_I
end ReciprocityTheory.L2DbarEstimates.H
end

set_option autoImplicit false
open Complex ComplexConjugate Filter Topology Matrix
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x ξ =
      ((Complex.normSq (∑ j, wd n j g x * ξ j) : ℝ) : ℂ) := by
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y := by
    filter_upwards [hg.eventually (by first | simp | decide | norm_num)] with y hy
    exact hy.differentiableAt (by first | norm_num | simp)
  have hdx : DifferentiableAt ℂ g x := hev.self_of_nhds
  have hhol : ∀ k, DifferentiableAt ℂ (wd n k g) x := by
    intro k
    have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by first | norm_num | rfl | simp)
    have h2 : DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n k)) x :=
      (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    rw [wd_eq_fderiv_basis_of_differentiableAt hy, hy.fderiv_restrictScalars ℝ]
    rfl
  have hterm : ∀ j k, wd n j (wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x =
      wd n j g x * conj (wd n k g x) := by
    intro j k
    have hc : wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
        fun y => g y * conj (wd n k g y) := by
      filter_upwards [hev] with y hy
      exact wdb_normSq_eq_mul_conj_wd hy
    rw [wd_apply_congr_of_eventuallyEq hc, wd_mul_conj_of_differentiableAt (hdx.restrictScalars ℝ) (hhol k)]
  unfold leviV
  simp only [hterm]
  rw [ofReal_normSq_sum_mul]
end ReciprocityTheory.L2DbarEstimates.H
