-- Prove2me | solution 1 for PermanentFormulaLowerBound.sum_matchingCrossPermutation_rows_cols
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/df8121a7-0d5d-471d-a949-23a2d4fe38c2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matching_card_residual_equiv
import Theorems.Thm_PermanentFormulaLowerBound_sum_matchingCrossPermutation

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {F T A B : Type*} [Semiring F]
    [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (hcard : Fintype.card A = Fintype.card B)
    (w : (T ↪ B) → (T ↪ A) → F) :
    (∑ σ : MatchingCrossPermutation T A B,
      w (matchingCrossRows σ) (matchingCrossCols σ)) =
      ((Fintype.card A - Fintype.card T).factorial : F) *
        ∑ rows : (T ↪ B), ∑ cols : (T ↪ A), w rows cols := by
  classical
  rw [sum_matchingCrossPermutation]
  calc
    (∑ rows : (T ↪ B), ∑ cols : (T ↪ A),
      ∑ remainder :
        ({a : A // a ∉ Set.range cols} ≃
          {b : B // b ∉ Set.range rows}),
        w (matchingCrossRows
            (MatchingCrossData.toPermutation ⟨rows, cols, remainder⟩))
          (matchingCrossCols
            (MatchingCrossData.toPermutation ⟨rows, cols, remainder⟩))) =
        ∑ rows : (T ↪ B), ∑ cols : (T ↪ A),
          ((Fintype.card A - Fintype.card T).factorial : F) *
            w rows cols := by
          apply Finset.sum_congr rfl
          intro rows _
          apply Finset.sum_congr rfl
          intro cols _
          have hres := matching_card_residual_equiv rows cols hcard
          simpa [matchingCrossRows_toPermutation,
            matchingCrossCols_toPermutation, nsmul_eq_mul] using
            congrArg (fun k : ℕ => (k : F) * w rows cols) hres
    _ = ((Fintype.card A - Fintype.card T).factorial : F) *
        ∑ rows : (T ↪ B), ∑ cols : (T ↪ A), w rows cols := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro rows _
          rw [Finset.mul_sum]
end PermanentFormulaLowerBound
