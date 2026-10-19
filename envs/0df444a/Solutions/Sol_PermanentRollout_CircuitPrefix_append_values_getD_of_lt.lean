-- Prove2me | solution 1 for PermanentRollout.CircuitPrefix.append_values_getD_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/ccb39d64-c114-4d20-8fd9-33aeb6b1480b

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_CircuitPrefix_values_size
import Theorems.Thm_PermanentRollout_CircuitPrefix_append_values

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
open PermanentRollout.CircuitPrefix
namespace PermanentRollout.CircuitPrefix
theorem _root_.solution {ι : Type} (state : CircuitPrefix ι)
    (instruction : Instruction ι)
    (hvalid : instruction.referencesBounded state.program.length)
    (index : ℕ) (hindex : index < state.program.length) :
    (state.append instruction hvalid).values.getD index 0 =
      state.values.getD index 0 := by
  rw [append_values]
  have hsize : index < state.values.size := by
    simpa [values_size] using hindex
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push,
    Nat.ne_of_lt hsize]
end PermanentRollout.CircuitPrefix
