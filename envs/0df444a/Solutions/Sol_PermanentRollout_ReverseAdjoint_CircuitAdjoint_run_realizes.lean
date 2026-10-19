-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.run_realizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/7d0fa153-e6df-424d-95f0-6b9203fb1bb1

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_foldl_realizes

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
    (circuit : FreeAffineCircuit ι) (output : FreeAffineForm ι) :
    (∀ gate, gate < circuit.program.length →
      (run circuit output).circuit.values.getD gate 0 =
        circuit.values.getD gate 0) ∧
    (∀ input,
      ((run circuit output).inputAdjoints input).eval
        (run circuit output).circuit.values =
          (ReverseAdjoint.run circuit output).inputAdjoints input) ∧
    (∀ gate,
      ((run circuit output).gateAdjoints gate).eval
        (run circuit output).circuit.values =
          (ReverseAdjoint.run circuit output).gateAdjoints gate) := by
  have hposition : ∀ instruction ∈ circuit.program.zipIdx.reverse,
      instruction.2 < (initial circuit output).sourceLength := by
    intro instruction hmem
    have hzip : instruction ∈ circuit.program.zipIdx := by
      simpa only [List.mem_reverse] using hmem
    rcases instruction with ⟨gate, position⟩
    obtain ⟨hposition, _⟩ := List.mem_zipIdx' hzip
    exact hposition
  have hvalid : ∀ instruction ∈ circuit.program.zipIdx.reverse,
      instruction.1.referencesBounded instruction.2 := by
    intro instruction hmem
    have hzip : instruction ∈ circuit.program.zipIdx := by
      simpa only [List.mem_reverse] using hmem
    rcases instruction with ⟨gate, position⟩
    obtain ⟨hposition, hgate⟩ := List.mem_zipIdx' hzip
    simpa [hgate] using circuit.valid ⟨position, hposition⟩
  have hforward : ∀ gate,
      gate < (initial circuit output).sourceLength →
        (initial circuit output).circuit.values.getD gate 0 =
          circuit.values.getD gate 0 := by
    intro gate hgate
    rfl
  have hinput : ∀ input,
      ((initial circuit output).inputAdjoints input).eval
          (initial circuit output).circuit.values =
        (ReverseAdjoint.initial output).inputAdjoints input := by
    intro input
    simp [CircuitAdjoint.initial, ReverseAdjoint.initial,
      ReverseAdjoint.scaleCoefficients_apply]
  have hgate : ∀ gate,
      ((initial circuit output).gateAdjoints gate).eval
          (initial circuit output).circuit.values =
        (ReverseAdjoint.initial output).gateAdjoints gate := by
    intro gate
    simp [CircuitAdjoint.initial, ReverseAdjoint.initial,
      ReverseAdjoint.scaleCoefficients_apply]
  simpa [run, ReverseAdjoint.run, CircuitAdjoint.initial] using
    foldl_realizes circuit.program.zipIdx.reverse
      (initial circuit output) (ReverseAdjoint.initial output)
      circuit.values hposition hvalid hforward hinput hgate
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
