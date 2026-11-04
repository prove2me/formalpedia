-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.evaluate_digits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:33.773709+00:00
-- url     : https://prove2.me/submissions/ee63d490-c021-46a1-a1a0-713af5ae0d64

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Theorems.Thm_ThreeSum_TernarySignedDigits_digit_quotient
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators
namespace ThreeSum.TernarySignedDigits
theorem _root_.solution (b x J : ℕ) :
    evaluate b J (fun j => (digit b x j : ℤ))=(x : ℤ)-(b : ℤ)^J*(quotient b x J : ℤ) := by
  induction J with
  | zero => simp [evaluate,quotient]
  | succ J ih =>
    simp only [evaluate,sum_range_succ] at ih ⊢
    rw [ih,digit_quotient,pow_succ]
    ring
end ThreeSum.TernarySignedDigits
