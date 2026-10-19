-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.eval_congr_of_referencesBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/e3d18b34-37dc-4092-a962-42546e1156b5

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
    (instruction : FreeAffineInstruction ι) (position : ℕ)
    (before after : Array (MvPolynomial ι ℂ))
    (hvalid : instruction.referencesBounded position)
    (hvalues : ∀ index < position,
      before.getD index 0 = after.getD index 0) :
    instruction.eval before = instruction.eval after := by
  classical
  cases instruction with
  | affine form =>
    simp only [FreeAffineInstruction.referencesBounded,
      decide_eq_true_eq] at hvalid
    simp only [FreeAffineInstruction.eval, FreeAffineForm.eval]
    congr 1
    simp only [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro index hindex
    rw [hvalues index (hvalid index hindex)]
  | mul left right =>
    simp only [FreeAffineInstruction.referencesBounded,
      Bool.and_eq_true, decide_eq_true_eq] at hvalid
    simp [FreeAffineInstruction.eval,
      hvalues left hvalid.1, hvalues right hvalid.2]
end PermanentRollout.ReverseAdjoint
