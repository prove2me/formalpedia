-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.instructionCost_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/6a5c9f6c-2e2a-4a6b-8a4d-73993f18db2a

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
    (program : List (FreeAffineInstruction ι)) :
    (program.map instructionCost).sum =
      2 * (program.filter FreeAffineInstruction.isMultiplication).length := by
  induction program with
  | nil => simp
  | cons instruction rest ih =>
    cases instruction with
    | affine form =>
      simpa [instructionCost, FreeAffineInstruction.isMultiplication,
        List.filter_cons] using ih
    | mul left right =>
      simp [instructionCost, FreeAffineInstruction.isMultiplication,
        ih, Nat.mul_add, Nat.add_comm]
end PermanentRollout.ReverseAdjoint
