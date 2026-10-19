-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.circuit_gateEquation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/b7003950-daad-4eae-b29c-cbdc36866f56

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_forwardFold_gateEquation

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
    (position : Fin circuit.program.length) :
    circuit.values.getD position.val 0 =
      (circuit.program.get position).eval circuit.values := by
  have hvalid : ∀ index : Fin circuit.program.length,
      (circuit.program.get index).referencesBounded
        ((#[] : Array (MvPolynomial ι ℂ)).size + index.val) := by
    intro index
    simpa using circuit.valid index
  change
    (circuit.program.foldl forwardStep
      (#[] : Array (MvPolynomial ι ℂ))).getD position.val 0 =
      (circuit.program.get position).eval
        (circuit.program.foldl forwardStep
          (#[] : Array (MvPolynomial ι ℂ)))
  simpa using
    forwardFold_gateEquation circuit.program
      (#[] : Array (MvPolynomial ι ℂ)) hvalid position
end PermanentRollout.ReverseAdjoint
