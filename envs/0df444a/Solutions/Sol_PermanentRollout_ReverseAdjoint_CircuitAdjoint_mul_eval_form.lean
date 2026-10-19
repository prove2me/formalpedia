-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.mul_eval_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/07a11b76-e00f-47f6-ab87-e03688ffdbfd

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_appendReverseProducts_eval_form

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
    (form : FreeAffineForm ι)
    (hform : ∀ index, form.gateCoefficients index ≠ 0 →
      index < state.circuit.program.length) :
    form.eval (state.mul position left right hleft hright).circuit.values =
      form.eval state.circuit.values := by
  rw [mul_circuit]
  exact appendReverseProducts_eval_form state.circuit
    (state.gateAdjoints position) left right
    (state.validGateAdjoints position)
    (Nat.lt_of_lt_of_le hleft state.sourceLength_le)
    (Nat.lt_of_lt_of_le hright state.sourceLength_le)
    form hform
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
