-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJAffinePoint_unitInverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:01:53.56989+00:00
-- url     : https://prove2.me/submissions/d25d84a5-6f99-4d81-b047-4467b9391034

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
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
    (R : Type) [CommRing R] (u : Rˣ) :
    lpsOriginalIntegerProjectiveJAffinePoint R false (u : R) =
      lpsOriginalIntegerProjectiveJAffinePoint R true ((u⁻¹ : Rˣ) : R) := by
  let φ : LaurentPolynomial ℤ →+* R := LaurentPolynomial.eval₂ (Int.castRingHom R) u
  have h0 : Polynomial.eval₂RingHom (Int.castRingHom R) (u : R) =
      φ.comp (Polynomial.toLaurent : Polynomial ℤ →+* LaurentPolynomial ℤ) := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simp [φ,RingHom.comp_apply,Polynomial.eval₂RingHom,Polynomial.toLaurent_X]
  have h1 : Polynomial.eval₂RingHom (Int.castRingHom R) ((u⁻¹ : Rˣ) : R) =
      φ.comp lpsOriginalIntegerReciprocalLaurentPolynomialMap := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simp [φ,RingHom.comp_apply,Polynomial.eval₂RingHom,
        lpsOriginalIntegerReciprocalLaurentPolynomialMap,Polynomial.toLaurent_X,
        LaurentPolynomial.invert_T]
  unfold lpsOriginalIntegerProjectiveJAffinePoint
  rw [h0,h1,CommRingCat.ofHom_comp,CommRingCat.ofHom_comp,Spec.map_comp,Spec.map_comp,
    Category.assoc,Category.assoc]
  exact congrArg (fun f : Spec (.of (LaurentPolynomial ℤ)) ⟶
    lpsOriginalIntegerProjectiveJLine => Spec.map (CommRingCat.ofHom φ) ≫ f)
    lpsOriginalIntegerProjectiveJOverlap_agreement
end QEC.Coding.TannerLiftedProduct
