-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.CircuitAdjoint.run_multiplicationCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/1fe0f126-c660-414a-82ef-19e32435907d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_instructionCost_sum
import Theorems.Thm_PermanentRollout_ReverseAdjoint_zipIdx_instructionCost_sum
import Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_foldl_multiplicationCount

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
    (run circuit output).circuit.multiplicationCount =
      3 * circuit.multiplicationCount := by
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
  unfold run
  rw [foldl_multiplicationCount _ _ hposition hvalid]
  simp only [initial, List.map_reverse, List.sum_reverse]
  rw [ReverseAdjoint.zipIdx_instructionCost_sum,
    ReverseAdjoint.instructionCost_sum]
  change
    circuit.multiplicationCount +
      2 * circuit.multiplicationCount =
        3 * circuit.multiplicationCount
  omega
end PermanentRollout.ReverseAdjoint.CircuitAdjoint
