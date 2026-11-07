-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJ_valuation_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:58:53.015208+00:00
-- url     : https://prove2.me/submissions/68420e15-ecd7-412d-ab2d-d268f549d089

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJ_specLocal_coordinate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJAffinePoint_baseChange
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJAffinePoint_fieldInverse
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
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (R K : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : Spec (.of K) ⟶ lpsOriginalIntegerProjectiveJLine) :
    ∃ g : Spec (.of R) ⟶ lpsOriginalIntegerProjectiveJLine,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ g=f := by
  obtain ⟨b,x,rfl⟩ := lpsOriginalIntegerProjectiveJ_specLocal_coordinate K f
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r,hr⟩ | ⟨r,hr⟩
  · refine ⟨lpsOriginalIntegerProjectiveJAffinePoint R b r,?_⟩
    rw [lpsOriginalIntegerProjectiveJAffinePoint_baseChange,hr]
  · by_cases hx : x=0
    · refine ⟨lpsOriginalIntegerProjectiveJAffinePoint R b 0,?_⟩
      rw [lpsOriginalIntegerProjectiveJAffinePoint_baseChange,map_zero,hx]
    · cases b with
      | false =>
          refine ⟨lpsOriginalIntegerProjectiveJAffinePoint R true r,?_⟩
          rw [lpsOriginalIntegerProjectiveJAffinePoint_baseChange,hr]
          exact (lpsOriginalIntegerProjectiveJAffinePoint_fieldInverse K x hx).symm
      | true =>
          refine ⟨lpsOriginalIntegerProjectiveJAffinePoint R false r,?_⟩
          rw [lpsOriginalIntegerProjectiveJAffinePoint_baseChange,hr]
          simpa using lpsOriginalIntegerProjectiveJAffinePoint_fieldInverse K x⁻¹ (inv_ne_zero hx)
end QEC.Coding.TannerLiftedProduct
