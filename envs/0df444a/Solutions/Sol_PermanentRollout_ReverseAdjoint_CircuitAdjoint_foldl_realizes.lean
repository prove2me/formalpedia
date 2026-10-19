-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.foldl_realizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/d4074758-b01b-4736-a5d0-ecc04878ab0f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_step_realizes

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
    (state : CircuitAdjoint ι) (adjoints : ReverseAdjoint ι)
    (sourceValues : Array (MvPolynomial ι ℂ))
    (hposition : ∀ instruction ∈ instructions,
      instruction.2 < state.sourceLength)
    (hvalid : ∀ instruction ∈ instructions,
      instruction.1.referencesBounded instruction.2)
    (hforward : ∀ gate, gate < state.sourceLength →
      state.circuit.values.getD gate 0 = sourceValues.getD gate 0)
    (hinput : ∀ input,
      (state.inputAdjoints input).eval state.circuit.values =
        adjoints.inputAdjoints input)
    (hgate : ∀ gate,
      (state.gateAdjoints gate).eval state.circuit.values =
        adjoints.gateAdjoints gate) :
    (∀ gate, gate < state.sourceLength →
      (instructions.foldl step state).circuit.values.getD gate 0 =
        sourceValues.getD gate 0) ∧
    (∀ input,
      ((instructions.foldl step state).inputAdjoints input).eval
        (instructions.foldl step state).circuit.values =
          (instructions.foldl
            (ReverseAdjoint.step sourceValues) adjoints).inputAdjoints
              input) ∧
    (∀ gate,
      ((instructions.foldl step state).gateAdjoints gate).eval
        (instructions.foldl step state).circuit.values =
          (instructions.foldl
            (ReverseAdjoint.step sourceValues) adjoints).gateAdjoints
              gate) := by
  induction instructions generalizing state adjoints with
  | nil =>
    exact ⟨hforward, hinput, hgate⟩
  | cons instruction rest ih =>
    have hheadPosition := hposition instruction (by simp)
    have hheadValid := hvalid instruction (by simp)
    obtain ⟨hnextForward, hnextInput, hnextGate⟩ :=
      step_realizes state adjoints sourceValues instruction
        hheadPosition hheadValid hforward hinput hgate
    have hrestPosition : ∀ gate ∈ rest,
        gate.2 < (step state instruction).sourceLength := by
      intro gate hmem
      rw [step_sourceLength]
      apply hposition gate
      simp [hmem]
    have hrestValid : ∀ gate ∈ rest,
        gate.1.referencesBounded gate.2 := by
      intro gate hmem
      apply hvalid gate
      simp [hmem]
    have hnextForward' : ∀ gate,
        gate < (step state instruction).sourceLength →
          (step state instruction).circuit.values.getD gate 0 =
            sourceValues.getD gate 0 := by
      intro gate hbound
      apply hnextForward gate
      simpa using hbound
    have hresult := ih (step state instruction)
      (ReverseAdjoint.step sourceValues adjoints instruction)
      hrestPosition hrestValid hnextForward' hnextInput hnextGate
    simpa [List.foldl_cons, step_sourceLength] using hresult
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
