-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.digit_quotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:59.534761+00:00
-- url     : https://prove2.me/submissions/4e36b382-7fd3-469d-9d96-da719ecdf342

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Theorems.Thm_ThreeSum_TernarySignedDigits_quotient_step

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators
namespace ThreeSum.TernarySignedDigits
theorem _root_.solution (b x j : ℕ) :
    (digit b x j : ℤ)=(quotient b x j : ℤ)-(b : ℤ)*(quotient b x (j+1) : ℤ) := by
  have hh : (digit b x j : ℤ)+(b : ℤ)*((quotient b x j/b : ℕ) : ℤ)=(quotient b x j : ℤ) := by
    exact_mod_cast Nat.mod_add_div (quotient b x j) b
  rw [quotient_step] at hh
  omega
end ThreeSum.TernarySignedDigits
