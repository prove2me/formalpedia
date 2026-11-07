-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalZeroChartToJLine_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:02:47.126004+00:00
-- url     : https://prove2.me/submissions/e1f8144c-967d-4790-b1ec-92f69d7cd3ee

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerBaseFractionMap_injective


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) :
    Surjective (lpsOriginalIntegerNormalZeroChartToJLine N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  constructor
  change Function.Surjective (PrimeSpectrum.comap (algebraMap (Polynomial ℤ)
    (lpsOriginalIntegerNormalZeroChart N hN)))
  have hinj : Function.Injective (algebraMap (Polynomial ℤ)
      (lpsOriginalIntegerNormalZeroChart N hN)) := by
    intro x y h
    have he := congrArg (fun a : lpsOriginalIntegerNormalZeroChart N hN =>
      (a : lpsOriginalGeneratedFunctionFieldQ N hN)) h
    change lpsOriginalIntegerBaseToGeneratedField N hN x =
      lpsOriginalIntegerBaseToGeneratedField N hN y at he
    change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalIntegerBaseFractionMap x) =
      algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalIntegerBaseFractionMap y) at he
    exact lpsOriginalIntegerBaseFractionMap_injective ((algebraMap
      (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)).injective he)
  let : FaithfulSMul (Polynomial ℤ) (lpsOriginalIntegerNormalZeroChart N hN) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact Algebra.IsIntegral.comap_surjective _ _
end QEC.Coding.TannerLiftedProduct
