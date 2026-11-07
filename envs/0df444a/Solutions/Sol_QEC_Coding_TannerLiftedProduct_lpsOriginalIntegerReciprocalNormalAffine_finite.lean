-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalNormalAffine_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:35:55.913257+00:00
-- url     : https://prove2.me/submissions/87ecd716-841d-48a2-8b63-601a7f5c1478

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalBase_isFractionRing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_finiteDimensional


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    Module.Finite (Polynomial ℤ)
      (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let : IsFractionRing (Polynomial ℤ) (FractionRing (Polynomial ℚ)) :=
    lpsOriginalIntegerReciprocalBase_isFractionRing
  let : IsScalarTower (Polynomial ℤ) (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hN) := .of_algebraMap_eq' rfl
  let : FiniteDimensional (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hN
  exact IsIntegralClosure.finite (Polynomial ℤ) (FractionRing (Polynomial ℚ))
    (lpsOriginalGeneratedFunctionFieldQ N hN)
    (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))
end QEC.Coding.TannerLiftedProduct
