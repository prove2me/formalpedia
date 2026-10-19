-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.run_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/0119c94c-aa7e-4fac-bd73-4b9ebf258c55

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_initial_potential
import Theorems.Thm_PermanentRollout_ReverseAdjoint_foldl_potential
import Theorems.Thm_PermanentRollout_ReverseAdjoint_circuit_gateEquation

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
namespace PermanentRollout.ReverseAdjoint
theorem _root_.solution {ι : Type*}
    (circuit : FreeAffineCircuit ι)
    (output : FreeAffineForm ι) (input : ι) :
    (run circuit output).potential circuit.values input =
      MvPolynomial.pderiv input (output.eval circuit.values) := by
  unfold run
  rw [foldl_potential]
  · exact initial_potential output circuit.values input
  · intro instruction hmem
    have hzip : instruction ∈ circuit.program.zipIdx := by
      simpa only [List.mem_reverse] using hmem
    rcases instruction with ⟨gate, position⟩
    obtain ⟨hposition, hgate⟩ := List.mem_zipIdx' hzip
    simpa [hgate] using
      circuit_gateEquation circuit ⟨position, hposition⟩
end PermanentRollout.ReverseAdjoint
