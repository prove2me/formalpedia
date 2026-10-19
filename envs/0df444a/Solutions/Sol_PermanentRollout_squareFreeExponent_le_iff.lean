-- Prove2me | solution 1 for PermanentRollout.squareFreeExponent_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/6f46437f-58e3-4ac0-a7a6-88450cab12bb

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {ι : Type*}
    (left right : Finset ι) :
    squareFreeExponent left ≤ squareFreeExponent right ↔ left ⊆ right := by
  classical
  constructor
  · intro h i hi
    by_contra hnot
    have hvalue := h i
    simp [squareFreeExponent_apply, hi, hnot] at hvalue
  · intro h i
    by_cases hi : i ∈ left
    · simp [squareFreeExponent_apply, hi, h hi]
    · simp [squareFreeExponent_apply, hi]
end PermanentRollout
