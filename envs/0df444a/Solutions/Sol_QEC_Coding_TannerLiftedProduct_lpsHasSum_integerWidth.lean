-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHasSum_integerWidth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:29:53.180189+00:00
-- url     : https://prove2.me/submissions/49bff6da-824c-4437-9ebf-3c0a2545f53c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_integerWidth_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)
    (h1 : (1:ℝ)∈Γ.strictPeriods) (m : ℕ) (hm : 0 < m) (f : ModularForm Γ k) (z : ℍ) :
    HasSum (fun n : ℕ => PowerSeries.coeff n
      ((UpperHalfPlane.qExpansion 1 f).expand m hm.ne')*
        Function.Periodic.qParam (m:ℝ) (z:ℂ)^n) (f z) := by
  let : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods (by norm_num) h1⟩
  let g : ℕ→ℂ := fun n => PowerSeries.coeff n
    ((UpperHalfPlane.qExpansion 1 f).expand m hm.ne')*
      Function.Periodic.qParam (m:ℝ) (z:ℂ)^n
  have hi : Function.Injective (fun n : ℕ => m*n) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hm hab
  have ho : ∀ n, n∉Set.range (fun a : ℕ => m*a) → g n=0 := by
    intro n hn
    have hnd : ¬m∣n := by rintro ⟨a,ha⟩;exact hn ⟨a,ha.symm⟩
    simp [g,PowerSeries.coeff_expand_of_not_dvd m hm.ne' _ hnd]
  have hf := ModularForm.hasSum_qExpansion f (by norm_num : (0:ℝ)<1) h1 z
  have hg : HasSum (g ∘ (fun n : ℕ => m*n)) (f z) := by
    apply hf.congr_fun
    intro n
    simp only [Function.comp_def,g,PowerSeries.coeff_expand_mul,pow_mul,lpsQParam_integerWidth_pow m hm]
  exact (hi.hasSum_iff ho).mp hg
end QEC.Coding.TannerLiftedProduct
