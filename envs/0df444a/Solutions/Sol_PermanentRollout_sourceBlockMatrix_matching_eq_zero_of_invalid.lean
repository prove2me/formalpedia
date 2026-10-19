-- Prove2me | solution 1 for PermanentRollout.sourceBlockMatrix_matching_eq_zero_of_invalid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/09b8646c-fe5f-422e-a093-52d4bde4ae09

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceBlockMatrix_matching_eq_zero_of_lower_right

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
namespace PermanentRollout
theorem _root_.solution
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (hinvalid : ¬ ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column) :
    (∏ row, sourceBlockMatrix r s d X U row (matching row)) = 0 := by
  obtain ⟨row, hrow⟩ := not_forall.mp hinvalid
  cases hcolumn : matching (.inr row) with
  | inl column =>
      exact (hrow ⟨column, hcolumn⟩).elim
  | inr column =>
      exact sourceBlockMatrix_matching_eq_zero_of_lower_right
        r s d X U matching row column hcolumn
end PermanentRollout
