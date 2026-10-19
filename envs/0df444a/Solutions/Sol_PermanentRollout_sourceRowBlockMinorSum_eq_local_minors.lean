-- Prove2me | solution 1 for PermanentRollout.sourceRowBlockMinorSum_eq_local_minors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/1970409f-5086-459e-b25d-1e58ab55c6ae

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceBlockMinor_sourceRowBlockEmbedding

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommSemiring R]
    (b t s d : ℕ) (h : Fin b)
    (X : Matrix (Fin (b * t)) (Fin s) R) :
    sourceRowBlockMinorSum b t s d X h =
      ∑ rows ∈ (Finset.univ : Finset (Fin t)).powersetCard d,
        ∑ columns ∈ (Finset.univ : Finset (Fin s)).powersetCard d,
          sourceBlockMinor t s
            (fun row column => X (sourceRowBlockEmbedding b t h row) column)
            rows columns := by
  classical
  unfold sourceRowBlockMinorSum
  rw [sourceRowBlock_eq_map,
    Finset.powersetCard_map]
  simp only [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro rows _
  apply Finset.sum_congr rfl
  intro columns _
  exact sourceBlockMinor_sourceRowBlockEmbedding b t s h X rows columns
end PermanentRollout
