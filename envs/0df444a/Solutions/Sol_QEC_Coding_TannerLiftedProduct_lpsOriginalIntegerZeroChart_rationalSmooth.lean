-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerZeroChart_rationalSmooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:19:41.32386+00:00
-- url     : https://prove2.me/submissions/1e794917-b8d7-4ef1-951f-56fc77f6ce0c

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCharacteristicZeroSmooth
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dedekindFiniteType_smoothCharZero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_finiteDimensional


set_option autoImplicit false
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI : Algebra ℤ (lpsOriginalIntegerNormalZeroChart N hpos) :=
      Ring.toIntAlgebra _
    letI : SMul ℤ (lpsOriginalIntegerNormalZeroChart N hpos) := Algebra.toSMul
    letI : Module ℤ (lpsOriginalIntegerNormalZeroChart N hpos) := Algebra.toModule
    Algebra.Smooth ℚ (ℚ ⊗[ℤ] lpsOriginalIntegerNormalZeroChart N hpos) := by
  let : Algebra ℤ (lpsOriginalIntegerNormalZeroChart N hpos) := Ring.toIntAlgebra _
  let : SMul ℤ (lpsOriginalIntegerNormalZeroChart N hpos) := Algebra.toSMul
  let : Module ℤ (lpsOriginalIntegerNormalZeroChart N hpos) := Algebra.toModule
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let J := FractionRing (Polynomial ℚ)
  let F := lpsOriginalGeneratedFunctionFieldQ N hpos
  let : Algebra (Polynomial ℚ) F :=
    ((algebraMap J F).comp (algebraMap (Polynomial ℚ) J)).toAlgebra
  let : IsScalarTower (Polynomial ℚ) J F := .of_algebraMap_eq' rfl
  let : IsScalarTower ℚ (Polynomial ℚ) F := inferInstance
  let : FiniteDimensional J F := lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hpos
  let R := integralClosure (Polynomial ℚ) F
  let : Algebra ℚ R := (R.restrictScalars ℚ).algebra
  let : IsDedekindDomain R := integralClosure.isDedekindDomain (Polynomial ℚ) J F
  let : Module.Finite (Polynomial ℚ) R :=
    IsIntegralClosure.finite (A := Polynomial ℚ) («K» := J) (L := F) R
  let : Algebra.FiniteType ℚ R := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℚ (Polynomial ℚ))
    (inferInstance : Algebra.FiniteType (Polynomial ℚ) R)
  let : Algebra.Smooth ℚ R :=
    QEC.Coding.AlgebraicGeometry.dedekindFiniteType_smoothCharZero ℚ R
  exact Algebra.Smooth.of_equiv
    (lpsOriginalIntegerZeroNormalizationRationalTensorAlgEquiv N hpos).symm
end QEC.Coding.TannerLiftedProduct
