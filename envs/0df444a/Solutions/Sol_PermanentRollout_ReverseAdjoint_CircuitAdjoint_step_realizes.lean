-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.step_realizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/a82a365b-e72f-44fb-a07c-995b1368a209

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_mul_values_getD_of_lt
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_affine_inputAdjoints_eval
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_affine_gateAdjoints_eval
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_mul_inputAdjoints_eval
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_mul_gateAdjoints_eval

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
    (state : CircuitAdjoint ι) (adjoints : ReverseAdjoint ι)
    (sourceValues : Array (MvPolynomial ι ℂ))
    (instruction : FreeAffineInstruction ι × ℕ)
    (hposition : instruction.2 < state.sourceLength)
    (hvalid : instruction.1.referencesBounded instruction.2)
    (hforward : ∀ gate, gate < state.sourceLength →
      state.circuit.values.getD gate 0 = sourceValues.getD gate 0)
    (hinput : ∀ input,
      (state.inputAdjoints input).eval state.circuit.values =
        adjoints.inputAdjoints input)
    (hgate : ∀ gate,
      (state.gateAdjoints gate).eval state.circuit.values =
        adjoints.gateAdjoints gate) :
    (∀ gate, gate < state.sourceLength →
      (step state instruction).circuit.values.getD gate 0 =
        sourceValues.getD gate 0) ∧
    (∀ input,
      ((step state instruction).inputAdjoints input).eval
        (step state instruction).circuit.values =
          (ReverseAdjoint.step sourceValues adjoints
            instruction).inputAdjoints input) ∧
    (∀ gate,
      ((step state instruction).gateAdjoints gate).eval
        (step state instruction).circuit.values =
          (ReverseAdjoint.step sourceValues adjoints
            instruction).gateAdjoints gate) := by
  classical
  rcases instruction with ⟨instruction, position⟩
  cases instruction with
  | affine form =>
    refine ⟨?_, ?_, ?_⟩
    · intro gate hbound
      exact hforward gate hbound
    · intro input
      change
        ((state.affine position form).inputAdjoints input).eval
            (state.affine position form).circuit.values =
          (adjoints.affine position form).inputAdjoints input
      rw [affine_inputAdjoints_eval,
        ReverseAdjoint.affine_inputAdjoints_apply,
        hinput input, hgate position]
    · intro gate
      change
        ((state.affine position form).gateAdjoints gate).eval
            (state.affine position form).circuit.values =
          (adjoints.affine position form).gateAdjoints gate
      rw [affine_gateAdjoints_eval]
      change
        (if gate = position then 0 else
          (state.gateAdjoints gate).eval state.circuit.values +
            MvPolynomial.C (form.gateCoefficients gate) *
              (state.gateAdjoints position).eval state.circuit.values) =
          (adjoints.gateAdjoints.erase position +
            ReverseAdjoint.scaleCoefficients
              (adjoints.gateAdjoints position)
              form.gateCoefficients) gate
      by_cases heq : gate = position
      · subst gate
        have hcoefficient : form.gateCoefficients position = 0 := by
          simp only [FreeAffineInstruction.referencesBounded,
            decide_eq_true_eq] at hvalid
          by_contra hnonzero
          have hlt := hvalid position
            (Finsupp.mem_support_iff.mpr hnonzero)
          omega
        simp [hcoefficient]
      · simp [heq, Finsupp.erase_ne heq,
          hgate gate, hgate position]
  | mul left right =>
    simp only [FreeAffineInstruction.referencesBounded,
      Bool.and_eq_true, decide_eq_true_eq] at hvalid
    have hbounds : left < state.sourceLength ∧
        right < state.sourceLength := by
      constructor <;> omega
    have hleftValue := hforward left hbounds.1
    have hrightValue := hforward right hbounds.2
    have hstep :
        step state (.mul left right, position) =
          state.mul position left right hbounds.1 hbounds.2 := by
      simp [step, hbounds]
    rw [hstep]
    refine ⟨?_, ?_, ?_⟩
    · intro gate hbound
      rw [mul_values_getD_of_lt state position left right
        hbounds.1 hbounds.2 gate
          (Nat.lt_of_lt_of_le hbound state.sourceLength_le)]
      exact hforward gate hbound
    · intro input
      change
        ((state.mul position left right hbounds.1 hbounds.2).inputAdjoints
          input).eval
            (state.mul position left right hbounds.1 hbounds.2).circuit.values =
              adjoints.inputAdjoints input
      rw [mul_inputAdjoints_eval]
      exact hinput input
    · intro gate
      rw [mul_gateAdjoints_eval]
      change
        (if gate = position then 0 else
          (state.gateAdjoints gate).eval state.circuit.values) +
        (if gate = left then
          (state.gateAdjoints position).eval state.circuit.values *
            state.circuit.values.getD right 0 else 0) +
        (if gate = right then
          (state.gateAdjoints position).eval state.circuit.values *
            state.circuit.values.getD left 0 else 0) =
        (adjoints.gateAdjoints.erase position +
          Finsupp.single left
            (adjoints.gateAdjoints position *
              sourceValues.getD right 0) +
          Finsupp.single right
            (adjoints.gateAdjoints position *
              sourceValues.getD left 0)) gate
      simp only [Finsupp.add_apply, Finsupp.erase_apply,
        Finsupp.single_apply, hgate gate, hgate position,
        hleftValue, hrightValue, eq_comm]
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
