-- Prove2me | solution 1 for PermanentRollout.CircuitPrefix.append_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/18269e36-91e7-445b-8454-18798741d42e

import Mathlib
import Definitions.Def_Permanent

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
    (state.append instruction hvalid).values =
      state.values.push (instruction.eval state.values) := by
  simp [values, append, List.foldl_append]
end PermanentRollout.CircuitPrefix
