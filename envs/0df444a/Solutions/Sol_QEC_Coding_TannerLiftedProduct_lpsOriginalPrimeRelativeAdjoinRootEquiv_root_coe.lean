-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeRelativeAdjoinRootEquiv_root_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:20:41.616677+00:00
-- url     : https://prove2.me/submissions/ca13cb8c-374f-4be5-9aa5-310e3e2750b9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
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
    ((lpsOriginalPrimeRelativeAdjoinRootEquiv N p hNp h4N hN
      (AdjoinRoot.root (lpsOriginalPrimeRelativeModularPolynomial N p hN
        (Fact.out : p.Prime).pos)) : lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :
            LPSOriginalHolomorphicFractionField) =
      lpsOriginalJNInFractionField (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let K := lpsOriginalGeneratedFunctionFieldQ N hN
  let x := lpsOriginalJNInFractionField (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  have hx : IsIntegral K x :=
    (lpsOriginalJNInFractionField_integralQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).tower_top
  let h := lpsOriginalGeneratedFunctionFieldQ_level_le N (N*p) (dvd_mul_right N p)
    h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  change ((IntermediateField.equivOfEq (IntermediateField.extendScalars_adjoin
      (show K ≤ IntermediateField.adjoin (FractionRing (Polynomial ℚ)) {x} from h)).symm)
    ((IntermediateField.adjoinRootEquivAdjoin K hx)
      ((AdjoinRoot.algEquivOfEq K _ _
        (lpsOriginalPrimeRelativeModularPolynomial_eq_minpoly N p hNp h4N hN))
        (AdjoinRoot.root _))) : LPSOriginalHolomorphicFractionField) = x
  rw [AdjoinRoot.algEquivOfEq_root, IntermediateField.adjoinRootEquivAdjoin_apply_root]
  rfl
end QEC.Coding.TannerLiftedProduct
