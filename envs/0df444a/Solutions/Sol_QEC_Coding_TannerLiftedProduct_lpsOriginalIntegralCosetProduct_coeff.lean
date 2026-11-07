-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegralCosetProduct_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:26:26.015905+00:00
-- url     : https://prove2.me/submissions/7eee4a8e-6c7c-4a2e-a201-6be9b7341f9a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
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
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {ι : Type*}
    (s : Finset ι) (f : ι→PowerSeries ℂ)
    (hf : ∀ i∈s, ∀ n, IsIntegral ℤ ((f i).coeff n)) (k n : ℕ) :
    IsIntegral ℤ (((∏ i∈s, (Polynomial.X-Polynomial.C (f i))).coeff k).coeff n) := by
  classical
  let T : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  let A : ι→PowerSeries T := fun i =>
    if hi : i∈s then (f i).toSubring T (hf i hi) else 0
  have hA : ∀ i∈s, (A i).map T.subtype=f i := by
    intro i hi
    simp only [A,dif_pos hi]
    ext n
    simp [PowerSeries.toSubring,PowerSeries.coeff_map]
  have he : ∏ i∈s, (Polynomial.X-Polynomial.C (f i))=
      (∏ i∈s, (Polynomial.X-Polynomial.C (A i))).map (PowerSeries.map T.subtype) := by
    rw [Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,hA i hi]
  rw [he,Polynomial.coeff_map,PowerSeries.coeff_map]
  exact (((∏ i∈s, (Polynomial.X-Polynomial.C (A i))).coeff k).coeff n).property
end QEC.Coding.TannerLiftedProduct
