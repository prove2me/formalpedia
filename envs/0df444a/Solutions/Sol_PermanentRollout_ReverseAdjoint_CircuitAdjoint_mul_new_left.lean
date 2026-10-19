-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.mul_new_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/746c5f3c-33ff-4f8d-8a4a-42ed89a84db2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_appendReverseProducts_values_left

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
open PermanentRollout.ReverseAdjoint.CircuitAdjoint
namespace PermanentRollout.ReverseAdjoint.CircuitAdjoint
theorem _root_.solution {ι : Type*}
    (state : CircuitAdjoint ι) (position left right : ℕ)
    (hleft : left < state.sourceLength)
    (hright : right < state.sourceLength) :
    (state.mul position left right hleft hright).circuit.values.getD
        (state.circuit.program.length + 2) 0 =
      (state.gateAdjoints position).eval state.circuit.values *
        state.circuit.values.getD left 0 := by
  rw [mul_circuit]
  exact appendReverseProducts_values_left state.circuit
    (state.gateAdjoints position) left right
    (state.validGateAdjoints position)
    (Nat.lt_of_lt_of_le hleft state.sourceLength_le)
    (Nat.lt_of_lt_of_le hright state.sourceLength_le)
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
