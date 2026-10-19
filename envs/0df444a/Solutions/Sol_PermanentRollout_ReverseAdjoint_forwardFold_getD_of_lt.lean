-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.forwardFold_getD_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/367ea1f8-8d4f-4965-8d6f-1bea16c5681c

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
    (values : Array (MvPolynomial ι ℂ))
    (index : ℕ) (hindex : index < values.size) :
    (program.foldl forwardStep values).getD index 0 =
      values.getD index 0 := by
  induction program generalizing values with
  | nil => rfl
  | cons instruction rest ih =>
    have hpush : index < (forwardStep values instruction).size := by
      simpa [forwardStep] using
        Nat.lt_trans hindex (Nat.lt_succ_self values.size)
    rw [List.foldl_cons, ih (forwardStep values instruction) hpush]
    simp [forwardStep, Array.getD_eq_getD_getElem?,
      Array.getElem?_push, Nat.ne_of_lt hindex]
end PermanentRollout.ReverseAdjoint
