-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalInfinityChartToJLine_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:03:06.434208+00:00
-- url     : https://prove2.me/submissions/4fe409c8-fb73-4709-9c6b-d71277b3e954

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalBaseFractionMap_injective


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalIntegerNormalInfinityChartToJLine N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  constructor
  change Function.Surjective (PrimeSpectrum.comap (algebraMap (Polynomial ℤ)
    (lpsOriginalIntegerNormalInfinityChart N hN)))
  have hinj : Function.Injective (algebraMap (Polynomial ℤ)
      (lpsOriginalIntegerNormalInfinityChart N hN)) := by
    intro x y h
    have he := congrArg (fun a : lpsOriginalIntegerNormalInfinityChart N hN =>
      (a : lpsOriginalGeneratedFunctionFieldQ N hN)) h
    change lpsOriginalIntegerReciprocalBaseToGeneratedField N hN x =
      lpsOriginalIntegerReciprocalBaseToGeneratedField N hN y at he
    change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalIntegerReciprocalBaseFractionMap x) =
      algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalIntegerReciprocalBaseFractionMap y) at he
    exact lpsOriginalIntegerReciprocalBaseFractionMap_injective ((algebraMap
      (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)).injective he)
  let : FaithfulSMul (Polynomial ℤ) (lpsOriginalIntegerNormalInfinityChart N hN) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact Algebra.IsIntegral.comap_surjective _ _
end QEC.Coding.TannerLiftedProduct
