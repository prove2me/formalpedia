-- Prove2me | solution 1 for PermanentRollout.CircuitInstructionReference.lt_of_referencesBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/7e8e0415-b9dd-4755-b355-714b8222826f

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
namespace CircuitInstructionReference
theorem _root_.solution
    {ι : Type} {instruction : Instruction ι} {index position : ℕ}
    (hreference : CircuitInstructionReference instruction index)
    (hvalid : instruction.referencesBounded position) :
    index < position := by
  cases hreference <;>
    simp_all [Instruction.referencesBounded, Bool.and_eq_true]
end CircuitInstructionReference
end PermanentRollout
