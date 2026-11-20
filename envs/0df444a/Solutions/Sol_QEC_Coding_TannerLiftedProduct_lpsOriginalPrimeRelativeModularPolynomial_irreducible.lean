-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeRelativeModularPolynomial_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:20:35.552061+00:00
-- url     : https://prove2.me/submissions/1e70fafc-fa43-4354-9c60-52619d4ca2eb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integralQ


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Irreducible (lpsOriginalPrimeRelativeModularPolynomial N p hN
      (Fact.out : p.Prime).pos) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalPrimeRelativeModularPolynomial_eq_minpoly N p hNp h4N hN]
  exact minpoly.irreducible ((lpsOriginalJNInFractionField_integralQ (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)).tower_top)
end QEC.Coding.TannerLiftedProduct
