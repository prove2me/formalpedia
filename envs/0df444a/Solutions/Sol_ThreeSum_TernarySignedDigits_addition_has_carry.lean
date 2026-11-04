-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.addition_has_carry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:41:56.258626+00:00
-- url     : https://prove2.me/submissions/0e018680-fc2f-4161-846e-a4549a725554

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Theorems.Thm_ThreeSum_TernarySignedDigits_addition_digit_carry
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryAt_canonical
import Theorems.Thm_ThreeSum_TernarySignedDigits_canonicalCarry_valid

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators
namespace ThreeSum.TernarySignedDigits
theorem _root_.solution {b J x y z : ℕ} (h : x+y=z) (hz : z<b^J) :
    ∃ c : CarryWord J, ValidCarry c ∧ DigitRelation b J x y z c := by
  refine ⟨canonicalCarry b x y J,canonicalCarry_valid (by omega),?_⟩
  intro j
  rw [carryAt_canonical (by omega),carryAt_canonical (by omega),← h]
  exact addition_digit_carry b x y j
end ThreeSum.TernarySignedDigits
