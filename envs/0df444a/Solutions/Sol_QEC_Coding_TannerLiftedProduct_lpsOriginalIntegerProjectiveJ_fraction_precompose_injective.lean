-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJ_fraction_precompose_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:59:27.3972+00:00
-- url     : https://prove2.me/submissions/507b63e2-4fcb-4479-9a9d-7a6801a0af5b

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJAffinePoint_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJAffinePoint_crossChart_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJAffinePoint_crossChart_of_mul
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
    [Algebra R K] [IsFractionRing R K] :
    Function.Injective (fun f : Spec (.of R) ⟶ lpsOriginalIntegerProjectiveJLine =>
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ f) := by
  intro f g h
  obtain ⟨b,x,rfl⟩ := lpsOriginalIntegerProjectiveJ_specLocal_coordinate R f
  obtain ⟨c,y,rfl⟩ := lpsOriginalIntegerProjectiveJ_specLocal_coordinate R g
  change Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      lpsOriginalIntegerProjectiveJAffinePoint R b x =
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      lpsOriginalIntegerProjectiveJAffinePoint R c y at h
  rw [lpsOriginalIntegerProjectiveJAffinePoint_baseChange,
    lpsOriginalIntegerProjectiveJAffinePoint_baseChange] at h
  cases b <;> cases c
  · have he := lpsOriginalIntegerProjectiveJAffinePoint_injective K false h
    rw [IsFractionRing.injective R K he]
  · have he := lpsOriginalIntegerProjectiveJAffinePoint_crossChart_mul K _ _ h
    have hr : x*y=1 := IsFractionRing.injective R K (by simpa only [map_mul,map_one] using he)
    exact lpsOriginalIntegerProjectiveJAffinePoint_crossChart_of_mul R x y hr
  · have he := lpsOriginalIntegerProjectiveJAffinePoint_crossChart_mul K _ _ h.symm
    have hr : y*x=1 := IsFractionRing.injective R K (by simpa only [map_mul,map_one] using he)
    exact (lpsOriginalIntegerProjectiveJAffinePoint_crossChart_of_mul R y x hr).symm
  · have he := lpsOriginalIntegerProjectiveJAffinePoint_injective K true h
    rw [IsFractionRing.injective R K he]
end QEC.Coding.TannerLiftedProduct
