-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.initial_gateAdjoints_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/bb6fbc26-bbf6-4d52-a7a8-8a251c21ad16

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
    (output : FreeAffineForm ι) (houtput : output ∈ circuit.outputs) :
    ∀ index, (initial output).gateAdjoints index ≠ 0 →
      index < circuit.program.length := by
  intro index hindex
  have hcoefficient : output.gateCoefficients index ≠ 0 := by
    intro hzero
    apply hindex
    simp [initial, scaleCoefficients_apply, hzero]
  exact circuit.validOutputs output houtput index hcoefficient
end PermanentRollout.ReverseAdjoint
