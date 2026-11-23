-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:20.514806+00:00
-- url     : https://prove2.me/submissions/efb3df08-6300-4747-a06f-dbdf647149d4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_eventually_differentiableAt_of_contDiffAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_fderiv_ofReal_apply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex ComplexConjugate Filter Topology
namespace ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
private theorem differentiableAt_fderiv_of_contDiffAt_two' {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (fderiv ℝ f) x :=
  (hf.fderiv_right (m := 1) one_add_one_eq_two.le).differentiableAt (by norm_num)
private theorem wirtinger_wirtingerBar_ofReal_lemma_2 {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) (j k : Fin n) :
    ReciprocityTheory.L2DbarEstimates.wd n j (ReciprocityTheory.L2DbarEstimates.wdb n k (fun y => (f y : ℂ))) x =
      (((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) +
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) -
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) / 4 := by
  have hD := differentiableAt_fderiv_of_contDiffAt_two' hf
  have hψ : ∀ a : ReciprocityTheory.L2DbarEstimates.V n, HasFDerivAt (fun y => ((fderiv ℝ f y a : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip a)) x := by
    intro a
    have h1 : HasFDerivAt (fun y => fderiv ℝ f y a) ((fderiv ℝ (fderiv ℝ f) x).flip a) x :=
      (hD.hasFDerivAt.clm_apply (hasFDerivAt_const a x)).congr_fderiv (by ext b; simp)
    exact (Complex.ofRealCLM.hasFDerivAt.comp x h1).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp)
  have hG : HasFDerivAt (fun y => (2⁻¹ : ℂ) * (((fderiv ℝ f y (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ f y (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)))
      ((2⁻¹ : ℂ) • (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip (ReciprocityTheory.L2DbarEstimates.bas n k)) +
        I • Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ f) x).flip (I • ReciprocityTheory.L2DbarEstimates.bas n k)))) x :=
    ((hψ (ReciprocityTheory.L2DbarEstimates.bas n k)).add ((hψ (I • ReciprocityTheory.L2DbarEstimates.bas n k)).const_mul I)).const_mul (2⁻¹ : ℂ)
  have hE : ReciprocityTheory.L2DbarEstimates.wdb n k (fun y => (f y : ℂ)) =ᶠ[𝓝 x] fun y =>
      (2⁻¹ : ℂ) * (((fderiv ℝ f y (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ f y (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) := by
    filter_upwards [ReciprocityTheory.L2DbarEstimates.eventually_differentiableAt_of_contDiffAt hf] with y hy
    rw [ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy, ReciprocityTheory.L2DbarEstimates.fderiv_ofReal_apply hy, div_eq_inv_mul]
  rw [ReciprocityTheory.L2DbarEstimates.wd_congr hE, ReciprocityTheory.L2DbarEstimates.wd, hG.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  push_cast
  linear_combination
    (-((fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) / 4) * I_sq
private theorem euclideanLeviForm_ofReal_eq_lemma_3 {f : ReciprocityTheory.L2DbarEstimates.V n → ℝ} {x : ReciprocityTheory.L2DbarEstimates.V n}
    (hf : ContDiffAt ℝ 2 f x) (ξ : Fin n → ℂ) :
    ReciprocityTheory.L2DbarEstimates.leviV n (fun y => (f y : ℂ)) x ξ =
      ∑ j, ∑ k, (((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) +
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ) +
        I * ((fderiv ℝ (fderiv ℝ f) x (ReciprocityTheory.L2DbarEstimates.bas n j) (I • ReciprocityTheory.L2DbarEstimates.bas n k) -
            fderiv ℝ (fderiv ℝ f) x (I • ReciprocityTheory.L2DbarEstimates.bas n j) (ReciprocityTheory.L2DbarEstimates.bas n k) : ℝ) : ℂ)) / 4 *
          ξ j * conj (ξ k) := by
  simp only [ReciprocityTheory.L2DbarEstimates.leviV, wirtinger_wirtingerBar_ofReal_lemma_2 hf]
private theorem re_div_four_mul_mul_conj_mul_four (P Q : ℝ) (z w : ℂ) :
    (((P : ℂ) + I * (Q : ℂ)) / 4 * z * conj w).re * 4 =
      P * (z.re * w.re + z.im * w.im) - Q * (z.im * w.re - z.re * w.im) := by
  have h4 : ((P : ℂ) + I * (Q : ℂ)) / 4 = ((P / 4 : ℝ) : ℂ) + I * ((Q / 4 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h4]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring
private theorem bilinear_apply_sum_sum (T : ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ReciprocityTheory.L2DbarEstimates.V n →L[ℝ] ℝ) (v w : Fin n → ReciprocityTheory.L2DbarEstimates.V n) :
    T (∑ j, v j) (∑ k, w k) = ∑ j, ∑ k, T (v j) (w k) := by
  have h : ∀ a : ReciprocityTheory.L2DbarEstimates.V n, T (∑ j, v j) a = ∑ j, T (v j) a := fun a => by
    rw [map_sum, ContinuousLinearMap.sum_apply]
  rw [h]
  exact Finset.sum_congr rfl fun j _ => map_sum (T (v j)) w Finset.univ
end ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
end

set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
theorem _root_.solution {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (ξ : Fin n → ℂ) :
    (leviV n (fun y => (f y : ℂ)) x ξ).re * 4 =
      fderiv ℝ (fderiv ℝ f) x (∑ k, ((ξ k).re • bas n k + (ξ k).im • (I • bas n k)))
          (∑ k, ((ξ k).re • bas n k + (ξ k).im • (I • bas n k))) +
      fderiv ℝ (fderiv ℝ f) x (∑ k, ((ξ k).re • (I • bas n k) - (ξ k).im • bas n k))
          (∑ k, ((ξ k).re • (I • bas n k) - (ξ k).im • bas n k)) := by
  rw [euclideanLeviForm_ofReal_eq_lemma_3 hf, bilinear_apply_sum_sum, bilinear_apply_sum_sum]
  simp only [Complex.re_sum, Finset.sum_mul, re_div_four_mul_mul_conj_mul_four]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative
