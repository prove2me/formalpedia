-- Prove2me | solution 1 for PermanentRollout.CircuitPrefix.append_values_getD_new
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/7a7fb0d8-3bb5-44a8-87ab-3c5eb5a14999

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
    (hvalid : instruction.referencesBounded state.program.length) :
    (state.append instruction hvalid).values.getD
      state.program.length 0 = instruction.eval state.values := by
  rw [append_values, ← values_size state]
  simp [Array.getD_eq_getD_getElem?]
end PermanentRollout.CircuitPrefix
