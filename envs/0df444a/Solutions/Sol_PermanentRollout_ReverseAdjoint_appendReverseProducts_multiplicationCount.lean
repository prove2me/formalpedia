-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.appendReverseProducts_multiplicationCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/3e82a525-3e0f-49aa-9886-1eb641e06843

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
    (circuit : FreeAffineCircuit ι) (adjoint : FreeAffineForm ι)
    (left right : ℕ)
    (hadjoint : ∀ index, adjoint.gateCoefficients index ≠ 0 →
      index < circuit.program.length)
    (hleft : left < circuit.program.length)
    (hright : right < circuit.program.length) :
    (appendReverseProducts circuit adjoint left right
      hadjoint hleft hright).multiplicationCount =
        circuit.multiplicationCount + 2 := by
  simp [appendReverseProducts, appendInstruction,
    FreeAffineCircuit.multiplicationCount,     FreeAffineInstruction.isMultiplication]
end PermanentRollout.ReverseAdjoint
