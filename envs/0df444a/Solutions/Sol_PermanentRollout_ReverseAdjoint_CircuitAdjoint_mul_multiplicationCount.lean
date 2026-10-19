-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.mul_multiplicationCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/90bfdcd3-4b0c-4824-b12a-6628b9741040

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_appendReverseProducts_multiplicationCount

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
    (state.mul position left right hleft hright).circuit.multiplicationCount =
      state.circuit.multiplicationCount + 2 := by
  exact appendReverseProducts_multiplicationCount state.circuit
    (state.gateAdjoints position) left right
    (state.validGateAdjoints position)
    (Nat.lt_of_lt_of_le hleft state.sourceLength_le)
    (Nat.lt_of_lt_of_le hright state.sourceLength_le)
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
