-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.mul_gateAdjoints_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/15bf7199-d7d0-4900-9591-f9f8d5f83a7a

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_mul_eval_form
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_mul_new_right
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_mul_new_left

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
    (hright : right < state.sourceLength) (gate : ℕ) :
    ((state.mul position left right hleft hright).gateAdjoints gate).eval
        (state.mul position left right hleft hright).circuit.values =
      (if gate = position then 0 else
        (state.gateAdjoints gate).eval state.circuit.values) +
      (if gate = left then
        (state.gateAdjoints position).eval state.circuit.values *
          state.circuit.values.getD right 0 else 0) +
      (if gate = right then
        (state.gateAdjoints position).eval state.circuit.values *
          state.circuit.values.getD left 0 else 0) := by
  have hold := mul_eval_form state position left right hleft hright
    (state.gateAdjoints gate) (state.validGateAdjoints gate)
  have hrightGate := mul_new_right state position left right hleft hright
  have hleftGate := mul_new_left state position left right hleft hright
  have hbase :
      (if gate = position then (0 : FreeAffineForm ι)
        else state.gateAdjoints gate).eval
          (state.mul position left right hleft hright).circuit.values =
        if gate = position then 0 else
          (state.gateAdjoints gate).eval state.circuit.values := by
    by_cases hgate : gate = position
    · simp only [hgate, ↓reduceIte, FreeAffineForm.eval_zero]
    · simp only [hgate, ↓reduceIte]
      exact hold
  have hrightForm :
      (if gate = left then
        FreeAffineForm.gate (state.circuit.program.length + 1)
      else (0 : FreeAffineForm ι)).eval
        (state.mul position left right hleft hright).circuit.values =
      if gate = left then
        (state.gateAdjoints position).eval state.circuit.values *
          state.circuit.values.getD right 0 else 0 := by
    by_cases hgate : gate = left
    · simp only [hgate, ↓reduceIte, FreeAffineForm.eval_gate]
      exact hrightGate
    · simp only [hgate, ↓reduceIte, FreeAffineForm.eval_zero]
  have hleftForm :
      (if gate = right then
        FreeAffineForm.gate (state.circuit.program.length + 2)
      else (0 : FreeAffineForm ι)).eval
        (state.mul position left right hleft hright).circuit.values =
      if gate = right then
        (state.gateAdjoints position).eval state.circuit.values *
          state.circuit.values.getD left 0 else 0 := by
    by_cases hgate : gate = right
    · simp only [hgate, ↓reduceIte, FreeAffineForm.eval_gate]
      exact hleftGate
    · simp only [hgate, ↓reduceIte, FreeAffineForm.eval_zero]
  rw [mul_gateAdjoints_apply, FreeAffineForm.eval_add,
    FreeAffineForm.eval_add, hbase, hrightForm, hleftForm]
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
