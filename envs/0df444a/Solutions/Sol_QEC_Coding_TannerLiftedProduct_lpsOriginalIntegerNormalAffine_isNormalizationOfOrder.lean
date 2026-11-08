-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalAffine_isNormalizationOfOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:15:02.397714+00:00
-- url     : https://prove2.me/submissions/0b30a872-6785-4d30-bd6c-5fa73753c8b1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerAffineToGenerated N hN).toAlgebra
    IsIntegralClosure
      (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))
      (lpsOriginalIntegerAffineRing N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalIntegerAffineToGenerated N hN).toAlgebra
  let : IsScalarTower (Polynomial ℤ) (lpsOriginalIntegerAffineRing N hN)
      (lpsOriginalGeneratedFunctionFieldQ N hN) :=
    .of_algebraMap_eq' (RingHom.ext (lpsOriginalIntegerAffineToGenerated_base N hN)).symm
  let := lpsOriginalIntegerAffineRing_finite N hN
  exact IsIntegralClosure.tower_top (R := Polynomial ℤ)
end QEC.Coding.TannerLiftedProduct
