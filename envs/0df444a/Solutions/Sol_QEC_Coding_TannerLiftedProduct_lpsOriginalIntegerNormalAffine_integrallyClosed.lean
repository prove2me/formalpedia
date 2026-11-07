-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalAffine_integrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:34:11.66562+00:00
-- url     : https://prove2.me/submissions/8b7e7df7-5445-4a6c-a933-0492d9388b29

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerBase_isFractionRing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_finiteDimensional


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerBaseFractionMap.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    IsIntegrallyClosed
      (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerBaseFractionMap.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let : IsFractionRing (Polynomial ℤ) (FractionRing (Polynomial ℚ)) :=
    lpsOriginalIntegerBase_isFractionRing
  let : IsScalarTower (Polynomial ℤ) (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hN) := .of_algebraMap_eq' rfl
  let : FiniteDimensional (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hN
  exact integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (Polynomial ℚ))
end QEC.Coding.TannerLiftedProduct
