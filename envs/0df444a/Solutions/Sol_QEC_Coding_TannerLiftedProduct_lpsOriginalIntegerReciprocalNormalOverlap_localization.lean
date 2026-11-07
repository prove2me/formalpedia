-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalNormalOverlap_localization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:42:50.553889+00:00
-- url     : https://prove2.me/submissions/216ea469-bb21-4f8d-a067-f5b2c1e440ef

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalLaurent_isLocalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalBaseFractionMap_X_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0<N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    let := lpsOriginalIntegerReciprocalLaurentBase_scalarTower N hN
    let := (lpsOriginalIntegerReciprocalNormalChartToOverlap N hN).toAlgebra
    IsLocalization.Away
      (algebraMap (Polynomial ℤ)
        (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) Polynomial.X)
      (integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentBase_scalarTower N hN
  let C := integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
  let D := integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
  let instCD : Algebra C D := (lpsOriginalIntegerReciprocalNormalChartToOverlap N hN).toAlgebra
  let : SMul C D := instCD.toSMul
  let : IsScalarTower C D (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    ⟨fun c d l => by
      change (c.val*d.val)*l=c.val*(d.val*l)
      exact mul_assoc _ _ _⟩
  let : IsScalarTower (Polynomial ℤ) C D := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro P
    apply Subtype.ext
    rfl
  have hx : algebraMap (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)
      Polynomial.X≠0 := by
    change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalIntegerReciprocalBaseFractionMap Polynomial.X)≠0
    exact (map_ne_zero_iff _ (algebraMap (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hN)).injective).mpr
        lpsOriginalIntegerReciprocalBaseFractionMap_X_ne_zero
  let : IsLocalization.Away
      (algebraMap (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) Polynomial.X)
      (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    IsLocalization.of_le_isUnit (fun y hy => by
      obtain ⟨n,rfl⟩ := hy
      exact (IsUnit.mk0 _ hx).pow n)
  let := lpsOriginalIntegerReciprocalLaurent_isLocalization
  exact IsLocalization.Away.integralClosure (R := Polynomial ℤ)
    (S := lpsOriginalGeneratedFunctionFieldQ N hN) (Rf := LaurentPolynomial ℤ)
    (Sf := lpsOriginalGeneratedFunctionFieldQ N hN) Polynomial.X
end QEC.Coding.TannerLiftedProduct
