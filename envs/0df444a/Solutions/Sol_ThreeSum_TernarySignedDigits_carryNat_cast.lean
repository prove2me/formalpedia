-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.carryNat_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:37:00.547374+00:00
-- url     : https://prove2.me/submissions/d74dd8d0-14ab-46fd-943b-1e72ca0da8fd

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
theorem _root_.solution (b x y j : ℕ) :
    (carryNat b x y j : ℤ)=(quotient b (x+y) j : ℤ)-(quotient b x j : ℤ)-(quotient b y j : ℤ) := by
  have hl := Nat.add_div_le_add_div x y (b^j)
  change quotient b x j+quotient b y j ≤ quotient b (x+y) j at hl
  unfold carryNat
  rw [Nat.cast_sub hl,Nat.cast_add]
  ring
end ThreeSum.TernarySignedDigits
