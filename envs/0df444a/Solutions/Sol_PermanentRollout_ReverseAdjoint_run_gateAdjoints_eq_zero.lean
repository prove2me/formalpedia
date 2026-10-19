-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.run_gateAdjoints_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/3af5a493-76e0-434a-958f-1a44f93b8d5f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_reverseFold_gateAdjoints_lt
import Theorems.Thm_PermanentRollout_ReverseAdjoint_initial_gateAdjoints_lt

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
    (output : FreeAffineForm ι) (houtput : output ∈ circuit.outputs) :
    (run circuit output).gateAdjoints = 0 := by
  have hvalid : ∀ instruction ∈ circuit.program.zipIdx,
      instruction.1.referencesBounded instruction.2 := by
    intro instruction hmem
    rcases instruction with ⟨gate, position⟩
    obtain ⟨hposition, hgate⟩ := List.mem_zipIdx' hmem
    simpa [hgate] using circuit.valid ⟨position, hposition⟩
  have hbound := reverseFold_gateAdjoints_lt circuit.program
    circuit.values 0 (initial output) hvalid
      (by simpa using initial_gateAdjoints_lt circuit output houtput)
  apply Finsupp.ext
  intro index
  change (run circuit output).gateAdjoints index = 0
  by_contra hnonzero
  have hlt : index < 0 := by
    apply hbound index
    exact hnonzero
  omega
end PermanentRollout.ReverseAdjoint
