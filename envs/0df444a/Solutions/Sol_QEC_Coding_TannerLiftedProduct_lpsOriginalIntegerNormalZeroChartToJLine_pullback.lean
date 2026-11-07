-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroChartToJLine_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:53:18.125849+00:00
-- url     : https://prove2.me/submissions/fcbe6df3-a822-437e-b28c-684412bd464d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalOverlap_localization


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0<N) :
    IsPullback (Spec.map (CommRingCat.ofHom (lpsOriginalIntegerNormalZeroToLaurent N hN)))
      (lpsOriginalIntegerNormalLaurentChartToJOverlap N hN)
      (lpsOriginalIntegerNormalZeroChartToJLine N hN)
      (lpsOriginalIntegerProjectiveJOverlapMap false) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerLaurentBase_scalarTower N hN
  let C := lpsOriginalIntegerNormalZeroChart N hN
  let B := lpsOriginalIntegerNormalLaurentChart N hN
  let instCB : Algebra C B := (lpsOriginalIntegerNormalZeroToLaurent N hN).toAlgebra
  let : SMul C B := instCB.toSMul
  let instAB : Algebra (Polynomial ℤ) B :=
    (integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)).algebra'
  let : SMul (Polynomial ℤ) B := instAB.toSMul
  let : IsScalarTower (Polynomial ℤ) C B := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro P
    apply Subtype.ext
    rfl
  let : IsScalarTower (Polynomial ℤ) (LaurentPolynomial ℤ) B := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro P
    apply Subtype.ext
    exact (lpsOriginalIntegerLaurentBaseToGeneratedField_polynomial N hN P).symm
  let : IsLocalization (Algebra.algebraMapSubmonoid C
      (Submonoid.powers (Polynomial.X : Polynomial ℤ))) B := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact lpsOriginalIntegerNormalOverlap_localization N hN
  let : Algebra.IsPushout (Polynomial ℤ) C (LaurentPolynomial ℤ) B :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers (Polynomial.X : Polynomial ℤ))
      (LaurentPolynomial ℤ) C B
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout (Polynomial ℤ) C (LaurentPolynomial ℤ) B)
end QEC.Coding.TannerLiftedProduct
