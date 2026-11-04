-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.evaluate_digits_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:37.599247+00:00
-- url     : https://prove2.me/submissions/7be875cb-c54d-4db5-9410-a1647c3efef1

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
import Theorems.Thm_ThreeSum_TernarySignedDigits_evaluate_digits
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators
namespace ThreeSum.TernarySignedDigits
theorem _root_.solution {b x J : ℕ} (h : x < b^J) :
    evaluate b J (fun j => (digit b x j : ℤ))=(x : ℤ) := by
  rw [evaluate_digits]
  simp [quotient,Nat.div_eq_of_lt h]
end ThreeSum.TernarySignedDigits
