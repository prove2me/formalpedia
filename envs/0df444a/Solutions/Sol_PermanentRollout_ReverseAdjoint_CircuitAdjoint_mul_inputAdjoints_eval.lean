-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.mul_inputAdjoints_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/c3198c08-17cf-489e-8f77-2162d56ab7b4

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_mul_eval_form

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
    (hright : right < state.sourceLength) (input : ι) :
    ((state.mul position left right hleft hright).inputAdjoints input).eval
        (state.mul position left right hleft hright).circuit.values =
      (state.inputAdjoints input).eval state.circuit.values := by
  rw [mul_inputAdjoints_apply]
  exact mul_eval_form state position left right hleft hright
    (state.inputAdjoints input) (state.validInputAdjoints input)
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
