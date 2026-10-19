-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.zipIdx_instructionCost_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/008c2fe6-9465-4a82-a259-3982133e4573

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
    (program : List (FreeAffineInstruction ι)) (start : ℕ) :
    ((program.zipIdx start).map (fun instruction =>
      instructionCost instruction.1)).sum =
      (program.map instructionCost).sum := by
  induction program generalizing start with
  | nil => simp
  | cons instruction rest ih =>
    simpa using congrArg (fun count : ℕ =>
      instructionCost instruction + count) (ih (start + 1))
end PermanentRollout.ReverseAdjoint
