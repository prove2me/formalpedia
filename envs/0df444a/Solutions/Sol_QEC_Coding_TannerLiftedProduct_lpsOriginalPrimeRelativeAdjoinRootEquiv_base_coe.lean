-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeRelativeAdjoinRootEquiv_base_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:31:55.307472+00:00
-- url     : https://prove2.me/submissions/fce339fd-24b3-4091-a9c9-6aa5b37bd538

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeAdjoinRootPresentation_base_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_level_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integralQ


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    ∀ c : lpsOriginalGeneratedFunctionFieldQ N hN,
    ((lpsOriginalPrimeRelativeAdjoinRootEquiv N p hNp h4N hN
      (algebraMap (lpsOriginalGeneratedFunctionFieldQ N hN)
        (AdjoinRoot (lpsOriginalPrimeRelativeModularPolynomial N p hN
          (Fact.out : p.Prime).pos)) c) : lpsOriginalGeneratedFunctionFieldQ (N*p)
            (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :
              LPSOriginalHolomorphicFractionField) = c := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  intro c
  exact lpsOriginalRelativeAdjoinRootPresentation_base_coe
    (lpsOriginalGeneratedFunctionFieldQ N hN)
    (lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN (Fact.out : p.Prime).pos))
    (lpsOriginalGeneratedFunctionFieldQ_level_le N (N*p) (dvd_mul_right N p)
      h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos))
    (lpsOriginalPrimeRelativeModularPolynomial N p hN (Fact.out : p.Prime).pos)
    (lpsOriginalPrimeRelativeModularPolynomial_eq_minpoly N p hNp h4N hN)
    ((lpsOriginalJNInFractionField_integralQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).tower_top) c
end QEC.Coding.TannerLiftedProduct
