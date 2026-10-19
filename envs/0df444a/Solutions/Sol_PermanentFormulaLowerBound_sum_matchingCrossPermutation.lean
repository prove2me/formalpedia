-- Prove2me | solution 1 for PermanentFormulaLowerBound.sum_matchingCrossPermutation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/48e13269-a3f8-478d-807e-fba94df28e1d

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {F T A B : Type*} [AddCommMonoid F]
    [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (w : MatchingCrossPermutation T A B → F) :
    (∑ σ : MatchingCrossPermutation T A B, w σ) =
      ∑ rows : (T ↪ B), ∑ cols : (T ↪ A),
        ∑ remainder :
          ({a : A // a ∉ Set.range cols} ≃
            {b : B // b ∉ Set.range rows}),
          w (MatchingCrossData.toPermutation
            ⟨rows, cols, remainder⟩) := by
  classical
  let e := matchingCrossPermutationSigmaEquiv (T := T) (A := A) (B := B)
  calc
    (∑ σ : MatchingCrossPermutation T A B, w σ) =
        ∑ z : (Σ rows : (T ↪ B), Σ cols : (T ↪ A),
          {a : A // a ∉ Set.range cols} ≃
            {b : B // b ∉ Set.range rows}), w (e.symm z) := by
          refine Fintype.sum_equiv e _ _ ?_
          intro σ
          simp
    _ = ∑ rows : (T ↪ B), ∑ cols : (T ↪ A),
        ∑ remainder :
          ({a : A // a ∉ Set.range cols} ≃
            {b : B // b ∉ Set.range rows}),
          w (MatchingCrossData.toPermutation
            ⟨rows, cols, remainder⟩) := by
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro rows _
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro cols _
          apply Finset.sum_congr rfl
          intro remainder _
          rfl
end PermanentFormulaLowerBound
