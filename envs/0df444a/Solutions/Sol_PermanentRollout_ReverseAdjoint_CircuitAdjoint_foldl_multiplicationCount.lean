-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.foldl_multiplicationCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/0b4e77aa-6617-4d57-9ec2-39414d05dc97

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_step_multiplicationCount

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
    (instructions : List (FreeAffineInstruction ι × ℕ))
    (state : CircuitAdjoint ι)
    (hposition : ∀ instruction ∈ instructions,
      instruction.2 < state.sourceLength)
    (hvalid : ∀ instruction ∈ instructions,
      instruction.1.referencesBounded instruction.2) :
    (instructions.foldl step state).circuit.multiplicationCount =
      state.circuit.multiplicationCount +
        (instructions.map (fun instruction =>
          ReverseAdjoint.instructionCost instruction.1)).sum := by
  induction instructions generalizing state with
  | nil => simp
  | cons instruction rest ih =>
    have hheadPosition := hposition instruction (by simp)
    have hheadValid := hvalid instruction (by simp)
    have hrestPosition : ∀ gate ∈ rest,
        gate.2 < (step state instruction).sourceLength := by
      intro gate hgate
      rw [step_sourceLength]
      apply hposition gate
      simp [hgate]
    have hrestValid : ∀ gate ∈ rest,
        gate.1.referencesBounded gate.2 := by
      intro gate hgate
      apply hvalid gate
      simp [hgate]
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih (step state instruction) hrestPosition hrestValid,
      step_multiplicationCount state instruction
        hheadPosition hheadValid]
    omega
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
