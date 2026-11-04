-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.carryNat_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:37:02.640873+00:00
-- url     : https://prove2.me/submissions/1eeefdbc-bf9c-4bf2-935c-d4465a8bb7f4

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
theorem _root_.solution {b x y J : ℕ} (h : x+y < b^J) : carryNat b x y J=0 := by
  unfold carryNat quotient
  rw [Nat.div_eq_of_lt h]
  exact Nat.zero_sub _
end ThreeSum.TernarySignedDigits
