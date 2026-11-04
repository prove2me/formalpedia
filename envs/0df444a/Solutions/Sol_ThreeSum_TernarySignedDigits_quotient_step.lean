-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.quotient_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:24:07.484706+00:00
-- url     : https://prove2.me/submissions/34535b1e-2318-42b1-9d9f-b5fb81c9bc10

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernarySignedDigits

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators
namespace ThreeSum.TernarySignedDigits
theorem _root_.solution (b x j : ℕ) : quotient b x j/b=quotient b x (j+1) := by
  unfold quotient
  rw [Nat.div_div_eq_div_mul,pow_succ]
end ThreeSum.TernarySignedDigits
