-- Prove2me | solution 1 for PermanentRollout.CircuitPrefix.exists_extension_computing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/ac64f662-007c-42df-aa77-f59789d421ef

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_CircuitPrefix_append_values_getD_of_lt
import Theorems.Thm_PermanentRollout_CircuitPrefix_append_values_getD_new

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
open PermanentRollout.CircuitPrefix
namespace PermanentRollout.CircuitPrefix
theorem _root_.solution {ι : Type}
    (polynomial : MvPolynomial ι ℂ) (state : CircuitPrefix ι) :
    ∃ (extension : CircuitPrefix ι) (output : ℕ),
      state.program.length ≤ extension.program.length ∧
      output < extension.program.length ∧
      extension.values.getD output 0 = polynomial ∧
      ∀ index : ℕ, index < state.program.length →
        extension.values.getD index 0 = state.values.getD index 0 := by
  induction polynomial using MvPolynomial.induction_on generalizing state with
  | C coefficient =>
    have hvalid :
        (Instruction.scalar coefficient : Instruction ι).referencesBounded
          state.program.length := by
      simp [Instruction.referencesBounded]
    let extension := state.append (.scalar coefficient) hvalid
    refine ⟨extension, state.program.length, ?_, ?_, ?_, ?_⟩
    · simp [extension, append]
    · simp [extension, append]
    · simpa [extension, Instruction.eval] using
        append_values_getD_new state (.scalar coefficient) hvalid
    · intro index hindex
      exact append_values_getD_of_lt state (.scalar coefficient)
        hvalid index hindex
  | add left right ihleft ihright =>
    obtain ⟨first, leftIndex, hprefixFirst, hleftIndex, hleft, hfirst⟩ :=
      ihleft state
    obtain ⟨second, rightIndex, hfirstSecond, hrightIndex, hright, hsecond⟩ :=
      ihright first
    have hleftSecond : leftIndex < second.program.length := by
      omega
    have hvalid :
        (Instruction.add leftIndex rightIndex : Instruction ι)
          |>.referencesBounded second.program.length := by
      simp [Instruction.referencesBounded, hleftSecond, hrightIndex]
    let extension := second.append (.add leftIndex rightIndex) hvalid
    refine ⟨extension, second.program.length, ?_, ?_, ?_, ?_⟩
    · simp only [extension, append, List.length_append,
        List.length_singleton]
      omega
    · simp [extension, append]
    · rw [show extension = second.append
          (.add leftIndex rightIndex) hvalid from rfl,
        append_values_getD_new]
      simp only [Instruction.eval]
      rw [hsecond leftIndex hleftIndex, hleft, hright]
    · intro index hindex
      have hfirstIndex : index < first.program.length := by
        omega
      have hsecondIndex : index < second.program.length := by omega
      rw [show extension = second.append
          (.add leftIndex rightIndex) hvalid from rfl,
        append_values_getD_of_lt second _ hvalid index hsecondIndex,
        hsecond index hfirstIndex, hfirst index hindex]
  | mul_X polynomial inputIndex ih =>
    obtain ⟨first, polynomialIndex, hprefixFirst, hpolynomialIndex,
      hpolynomial, hfirst⟩ := ih state
    have hinput :
        (Instruction.input inputIndex : Instruction ι).referencesBounded
          first.program.length := by
      simp [Instruction.referencesBounded]
    let second := first.append (.input inputIndex) hinput
    have hpolynomialSecond : polynomialIndex < second.program.length := by
      simpa [second, append] using Nat.lt_succ_of_lt hpolynomialIndex
    have hvariableSecond : first.program.length < second.program.length := by
      simp [second, append]
    have hmul :
        (Instruction.mul polynomialIndex first.program.length : Instruction ι)
          |>.referencesBounded second.program.length := by
      simp [Instruction.referencesBounded, hpolynomialSecond, hvariableSecond]
    let extension := second.append
      (.mul polynomialIndex first.program.length) hmul
    refine ⟨extension, second.program.length, ?_, ?_, ?_, ?_⟩
    · simp only [extension, second, append, List.length_append,
        List.length_singleton]
      omega
    · simp [extension, append]
    · rw [show extension = second.append
          (.mul polynomialIndex first.program.length) hmul from rfl,
        append_values_getD_new]
      simp only [Instruction.eval]
      rw [show second = first.append (.input inputIndex) hinput from rfl,
        append_values_getD_of_lt first _ hinput
          polynomialIndex hpolynomialIndex,
        append_values_getD_new first (.input inputIndex) hinput,
        hpolynomial]
      rfl
    · intro index hindex
      have hfirstIndex : index < first.program.length := by
        omega
      have hsecondIndex : index < second.program.length := by
        simpa [second, append] using Nat.lt_succ_of_lt hfirstIndex
      rw [show extension = second.append
          (.mul polynomialIndex first.program.length) hmul from rfl,
        append_values_getD_of_lt second _ hmul index hsecondIndex,
        show second = first.append (.input inputIndex) hinput from rfl,
        append_values_getD_of_lt first _ hinput index hfirstIndex,
        hfirst index hindex]
end PermanentRollout.CircuitPrefix
