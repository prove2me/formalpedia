-- Prove2me | solution 1 for PermanentRollout.sourceBlockMatrix_matching_eq_zero_of_lower_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/1bb8dec0-c321-4781-bc78-e34b0c183ced

import Mathlib
import Definitions.Def_Permanent

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
    (row : Fin (s - d)) (column : Fin (r - d))
    (h : matching (.inr row) = .inr column) :
    (∏ i, sourceBlockMatrix r s d X U i (matching i)) = 0 := by
  classical
  apply Finset.prod_eq_zero (Finset.mem_univ (.inr row))
  simp [h]
end PermanentRollout
