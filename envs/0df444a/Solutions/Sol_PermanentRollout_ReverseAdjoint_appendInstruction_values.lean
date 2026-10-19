-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.appendInstruction_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/977a1e82-ebef-462d-8906-2b5db0533f06

import Mathlib
import Definitions.Def_Permanent

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
    (instruction : FreeAffineInstruction ι)
    (hvalid : instruction.referencesBounded circuit.program.length) :
    (appendInstruction circuit instruction hvalid).values =
      circuit.values.push (instruction.eval circuit.values) := by
  change
    ((circuit.program ++ [instruction]).foldl forwardStep
      (#[] : Array (MvPolynomial ι ℂ))) =
      (circuit.program.foldl forwardStep
        (#[] : Array (MvPolynomial ι ℂ))).push
          (instruction.eval
            (circuit.program.foldl forwardStep
              (#[] : Array (MvPolynomial ι ℂ))))
  simp [List.foldl_append, forwardStep]
end PermanentRollout.ReverseAdjoint
