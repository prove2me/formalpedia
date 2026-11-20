-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAdjoinRootPrimePowerFrobeniusDescent_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:56:53.414634+00:00
-- url     : https://prove2.me/submissions/9378cc9d-76eb-4b28-869a-7cb3f53d82f6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAdjoinRootPrimePower_root
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
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K)
    [Fact (Irreducible ((Polynomial.X : Polynomial K)^p - Polynomial.C a))]
    (x : AdjoinRoot ((Polynomial.X : Polynomial K)^p - Polynomial.C a)) :
    AdjoinRoot.of ((Polynomial.X : Polynomial K)^p - Polynomial.C a)
      (lpsOriginalAdjoinRootPrimePowerFrobeniusDescent p a x) = x^p := by
  let Q : Polynomial K := Polynomial.X^p - Polynomial.C a
  let T := AdjoinRoot Q
  let : CharP T p := charP_of_injective_algebraMap (algebraMap K T).injective p
  have hroot := lpsOriginalAdjoinRootPrimePower_root p a
  have hcomm : (AdjoinRoot.of Q).comp (frobenius K p) =
      (frobenius T p).comp (AdjoinRoot.of Q) := by
    ext c
    simp [frobenius_def]
  induction x using AdjoinRoot.induction_on with
  | ih f =>
    rw [lpsOriginalAdjoinRootPrimePowerFrobeniusDescent, AdjoinRoot.lift_mk]
    calc
      AdjoinRoot.of Q (f.eval₂ (frobenius K p) a) =
          f.eval₂ ((AdjoinRoot.of Q).comp (frobenius K p)) (AdjoinRoot.of Q a) :=
        Polynomial.hom_eval₂ _ _ _ _
      _ = f.eval₂ ((frobenius T p).comp (AdjoinRoot.of Q))
          (frobenius T p (AdjoinRoot.root Q)) := by rw [hcomm, frobenius_def, hroot]
      _ = frobenius T p (f.eval₂ (AdjoinRoot.of Q) (AdjoinRoot.root Q)) :=
        (Polynomial.hom_eval₂ _ _ _ _).symm
      _ = (AdjoinRoot.mk Q f)^p := by
        rw [frobenius_def]
        congr 1
        exact (AdjoinRoot.aeval_eq f).trans rfl
end QEC.Coding.TannerLiftedProduct
