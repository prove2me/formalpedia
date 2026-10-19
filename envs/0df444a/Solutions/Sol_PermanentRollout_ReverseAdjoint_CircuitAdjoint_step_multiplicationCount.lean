-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.step_multiplicationCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/5511392e-6a52-4d2c-b7ac-8a0b63fd37f8

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_mul_multiplicationCount

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
    (state : CircuitAdjoint ι)
    (instruction : FreeAffineInstruction ι × ℕ)
    (hposition : instruction.2 < state.sourceLength)
    (hvalid : instruction.1.referencesBounded instruction.2) :
    (step state instruction).circuit.multiplicationCount =
      state.circuit.multiplicationCount +
        ReverseAdjoint.instructionCost instruction.1 := by
  rcases instruction with ⟨instruction, position⟩
  cases instruction with
  | affine form =>
    change state.circuit.multiplicationCount = _
    simp [ReverseAdjoint.instructionCost]
  | mul left right =>
    simp only [FreeAffineInstruction.referencesBounded,
      Bool.and_eq_true, decide_eq_true_eq] at hvalid
    have hbounds : left < state.sourceLength ∧
        right < state.sourceLength := by
      constructor <;> omega
    simpa [step, hbounds, ReverseAdjoint.instructionCost] using
      mul_multiplicationCount state position left right
        hbounds.1 hbounds.2
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
