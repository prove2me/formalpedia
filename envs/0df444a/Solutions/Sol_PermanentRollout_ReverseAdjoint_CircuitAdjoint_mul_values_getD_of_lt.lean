-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.mul_values_getD_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/a44d1cac-4852-4f63-94c9-bd89867bd8d0

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_appendReverseProducts_values_getD_of_lt

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
    (hright : right < state.sourceLength)
    (gate : ℕ) (hgate : gate < state.circuit.program.length) :
    (state.mul position left right hleft hright).circuit.values.getD
        gate 0 = state.circuit.values.getD gate 0 := by
  rw [mul_circuit]
  exact appendReverseProducts_values_getD_of_lt state.circuit
    (state.gateAdjoints position) left right
    (state.validGateAdjoints position)
    (Nat.lt_of_lt_of_le hleft state.sourceLength_le)
    (Nat.lt_of_lt_of_le hright state.sourceLength_le) gate hgate
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
