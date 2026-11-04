-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.addition_digit_carry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:32.731729+00:00
-- url     : https://prove2.me/submissions/88d3cf67-5e17-4d1d-906f-f230c6e09a45

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Theorems.Thm_ThreeSum_TernarySignedDigits_digit_quotient
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_cast

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators
namespace ThreeSum.TernarySignedDigits
theorem _root_.solution (b x y j : ℕ) :
    (digit b x j : ℤ)+(digit b y j : ℤ)+(carryNat b x y j : ℤ)=
      (digit b (x+y) j : ℤ)+(b : ℤ)*(carryNat b x y (j+1) : ℤ) := by
  simp only [digit_quotient,carryNat_cast]
  ring
end ThreeSum.TernarySignedDigits
