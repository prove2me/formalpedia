-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQExpansion_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:01.942056+00:00
-- url     : https://prove2.me/submissions/b1dd10f1-f076-4ac9-bace-81b67ae7174d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSFourierPeriodChange
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspFunction_prod_analytic
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
theorem _root_.solution {ι : Type*} (h : ℝ) (s : Finset ι) (F : ι→ℍ→ℂ)
    (ha : ∀i∈s,AnalyticAt ℂ (UpperHalfPlane.cuspFunction h (F i)) 0) :
    UpperHalfPlane.qExpansion h (∏i∈s,F i)=∏i∈s,UpperHalfPlane.qExpansion h (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,UpperHalfPlane.qExpansion_one]
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self _ _)
    have has : ∀j∈s,AnalyticAt ℂ (UpperHalfPlane.cuspFunction h (F j)) 0 :=
      fun j hj => ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,Finset.prod_insert hi,
      UpperHalfPlane.qExpansion_mul hai (lpsCuspFunction_prod_analytic h s F has),ih has]
end QEC.Coding.TannerLiftedProduct
