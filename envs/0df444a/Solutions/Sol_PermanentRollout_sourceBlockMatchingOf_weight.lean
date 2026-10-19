-- Prove2me | solution 1 for PermanentRollout.sourceBlockMatchingOf_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/d681c17a-de01-40e3-aea4-94c2fcada055

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
    (I : Finset (Fin r)) (J : Finset (Fin s))
    (variableMatching : I ≃ J)
    (constantMatching : {row : Fin r // row ∉ I} ≃ Fin (r - d))
    (onesMatching : Fin (s - d) ≃ {column : Fin s // column ∉ J}) :
    (∏ row, sourceBlockMatrix r s d X U row
      (sourceBlockMatchingOf r s d I J
        variableMatching constantMatching onesMatching row)) =
      (∏ row : I, X row.val (variableMatching row).val) *
        (∏ row : {row : Fin r // row ∉ I},
          U row.val (constantMatching row)) := by
  rw [Fintype.prod_sum_type]
  rw [← (Equiv.sumCompl (fun row : Fin r => row ∈ I)).prod_comp
    (fun row : Fin r =>
      sourceBlockMatrix r s d X U (.inl row)
        (sourceBlockMatchingOf r s d I J
          variableMatching constantMatching onesMatching (.inl row)))]
  rw [Fintype.prod_sum_type]
  simp
end PermanentRollout
