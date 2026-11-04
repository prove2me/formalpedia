-- Prove2me | solution 1 for ThreeSum.TernarySignedReduction.tagged_relation_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:41:46.270306+00:00
-- url     : https://prove2.me/submissions/77fcf27a-f8ce-4d04-9078-2fc385746076

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero


attribute [local simp] ThreeSum.TernarySignedReduction.mem_carryCatalog

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset
namespace ThreeSum.TernarySignedReduction
theorem _root_.solution (U radix J : ℕ) (a b c : ℤ) (carry : CarryWord J) :
    (∀ k, leftRaw U radix J b k+rightRaw U radix J c k=requesterRaw U radix J a carry k) ↔
      DigitRelation radix J (shiftOne U b) (shiftOne U a) (shiftTwo U c) carry := by
  constructor
  · intro h j
    have hh := h (.inl j)
    simp only [leftRaw,rightRaw,requesterRaw] at hh
    linarith
  · intro h k
    cases k with
    | inl j =>
      have hh := h j
      simp only [leftRaw,rightRaw,requesterRaw]
      linarith
    | inr t => cases t <;> norm_num [leftRaw,rightRaw,requesterRaw]
end ThreeSum.TernarySignedReduction
