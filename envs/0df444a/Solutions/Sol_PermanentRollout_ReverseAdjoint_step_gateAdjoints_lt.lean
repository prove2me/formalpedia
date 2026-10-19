-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.step_gateAdjoints_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/d2b516a6-6ca9-4061-84dd-f1f1ffca6176

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
    (values : Array (MvPolynomial ι ℂ))
    (state : ReverseAdjoint ι)
    (instruction : FreeAffineInstruction ι) (position : ℕ)
    (hvalid : instruction.referencesBounded position)
    (hstate : ∀ index, state.gateAdjoints index ≠ 0 →
      index < position + 1) :
    ∀ index,
      (step values state (instruction, position)).gateAdjoints index ≠ 0 →
        index < position := by
  classical
  intro index hnonzero
  by_contra hlt
  have hge : position ≤ index := Nat.le_of_not_gt hlt
  have herase : (state.gateAdjoints.erase position) index = 0 := by
    by_cases heq : index = position
    · subst index
      simp
    · rw [Finsupp.erase_ne heq]
      by_contra hindex
      have hbound := hstate index hindex
      omega
  cases instruction with
  | affine form =>
    simp only [FreeAffineInstruction.referencesBounded,
      decide_eq_true_eq] at hvalid
    have hcoefficient : form.gateCoefficients index = 0 := by
      by_contra hcoefficient
      have hbound := hvalid index
        (Finsupp.mem_support_iff.mpr hcoefficient)
      omega
    simp [step, affine, herase, hcoefficient] at hnonzero
  | mul left right =>
    simp only [FreeAffineInstruction.referencesBounded,
      Bool.and_eq_true, decide_eq_true_eq] at hvalid
    have hleft : left ≠ index := by omega
    have hright : right ≠ index := by omega
    simp [step, mul, herase, hleft, hright] at hnonzero
end PermanentRollout.ReverseAdjoint
