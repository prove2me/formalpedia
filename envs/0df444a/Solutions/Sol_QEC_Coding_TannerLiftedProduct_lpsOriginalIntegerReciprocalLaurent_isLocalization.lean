-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalLaurent_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:39:56.550208+00:00
-- url     : https://prove2.me/submissions/b95a052f-555a-4692-b61c-ad59c2cabdad

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalLaurentPolynomialMap_injective
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
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    IsLocalization.Away (Polynomial.X : Polynomial ℤ) (LaurentPolynomial ℤ) := by
  have hu (b : Submonoid.powers (Polynomial.X : Polynomial ℤ)) :
      IsUnit (Polynomial.toLaurent (b : Polynomial ℤ)) :=
    IsLocalization.map_units (S := LaurentPolynomial ℤ) b
  have hs (z : LaurentPolynomial ℤ) : ∃ p : Polynomial ℤ ×
      Submonoid.powers (Polynomial.X : Polynomial ℤ),
        z*Polynomial.toLaurent (p.2 : Polynomial ℤ)=Polynomial.toLaurent p.1 :=
    IsLocalization.surj (Submonoid.powers (Polynomial.X : Polynomial ℤ)) z
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  refine
    { map_units := fun b => ?_
      surj := fun z => ?_
      exists_of_eq := fun {x y} h => ?_ }
  · change IsUnit (LaurentPolynomial.invert (Polynomial.toLaurent (b : Polynomial ℤ)))
    exact (hu b).map (LaurentPolynomial.invert (R := ℤ)).toRingHom
  · obtain ⟨p,hp⟩ := hs (LaurentPolynomial.invert z)
    refine ⟨p,?_⟩
    change z*LaurentPolynomial.invert (Polynomial.toLaurent (p.2 : Polynomial ℤ))=
      LaurentPolynomial.invert (Polynomial.toLaurent p.1)
    have hh := congrArg (fun w : LaurentPolynomial ℤ => LaurentPolynomial.invert w) hp
    rw [map_mul] at hh
    have hz : LaurentPolynomial.invert (LaurentPolynomial.invert z)=z :=
      LaurentPolynomial.involutive_invert z
    rw [hz] at hh
    exact hh
  · have hxy := lpsOriginalIntegerReciprocalLaurentPolynomialMap_injective h
    refine ⟨1,?_⟩
    simpa only [Submonoid.coe_one,one_mul] using hxy
end QEC.Coding.TannerLiftedProduct
