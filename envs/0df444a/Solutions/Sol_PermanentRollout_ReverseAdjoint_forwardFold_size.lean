-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.forwardFold_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/ccea10de-f7a4-4394-971c-1764adfb383f

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
    (program : List (FreeAffineInstruction ι))
    (values : Array (MvPolynomial ι ℂ)) :
    (program.foldl forwardStep values).size =
      values.size + program.length := by
  induction program generalizing values with
  | nil => simp
  | cons instruction rest ih =>
    simpa [List.foldl_cons, forwardStep, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using
      ih (forwardStep values instruction)
end PermanentRollout.ReverseAdjoint
