-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2Dilated_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:27:00.549334+00:00
-- url     : https://prove2.me/submissions/3896b22e-f083-4a72-81f1-717beba0a030

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_qParam
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m : ℕ) (hm : 0 < m) (z : ℍ) :
    HasSum (fun n : ℕ => lpsE2DilationCoefficient m n*Function.Periodic.qParam 1 (z:ℂ)^n)
      (EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • z)) := by
  let f : ℕ→ℂ := fun n => lpsE2DilationCoefficient m n*Function.Periodic.qParam 1 (z:ℂ)^n
  have hi : Function.Injective (fun n : ℕ => m*n) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hm hab
  have ho : ∀ n, n∉Set.range (fun k : ℕ => m*k) → f n=0 := by
    intro n hn
    have hnd : ¬m∣n := by
      rintro ⟨k,hk⟩
      exact hn ⟨k,hk.symm⟩
    simp [f,lpsE2DilationCoefficient,hnd]
  have hs : HasSum (fun n : ℕ => (if n=0 then 1 else -24*(ArithmeticFunction.sigma 1 n:ℂ))*
      Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm 0 • z:ℍ):ℂ)^n)
      (EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • z)) := by
    simpa only [smul_eq_mul,Function.Periodic.qParam,Complex.ofReal_one,div_one] using
      EisensteinSeries.hasSum_qExpansion_E2 (z:=lpsE2AffineMatrix m hm 0 • z)
  rw [lpsE2AffineMatrix_qParam] at hs
  have hcomp : HasSum (f ∘ (fun n : ℕ => m*n))
      (EisensteinSeries.E2 (lpsE2AffineMatrix m hm 0 • z)) := by
    apply hs.congr_fun
    intro n
    have hd : m∣m*n := dvd_mul_right _ _
    have hdiv : m*n/m=n := Nat.mul_div_cancel_left n hm
    simp only [Function.comp_def,f,lpsE2DilationCoefficient,if_pos hd,hdiv,pow_mul]
  exact (hi.hasSum_iff ho).mp hcomp
end QEC.Coding.TannerLiftedProduct
