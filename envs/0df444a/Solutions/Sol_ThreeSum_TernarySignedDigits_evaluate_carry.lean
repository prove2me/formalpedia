-- Prove2me | solution 1 for ThreeSum.TernarySignedDigits.evaluate_carry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:35.068682+00:00
-- url     : https://prove2.me/submissions/22065620-5ba2-4f37-b014-5dd9548d02f1

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_zero
attribute [local simp] ThreeSum.TernarySignedDigits.carryNat_zero

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators
namespace ThreeSum.TernarySignedDigits
theorem _root_.solution (b J : ℕ) (c : ℕ → ℤ) :
    evaluate b J (fun j => (b : ℤ)*c (j+1)-c j)=(b : ℤ)^J*c J-c 0 := by
  induction J with
  | zero => simp [evaluate]
  | succ J ih =>
    simp only [evaluate,sum_range_succ] at ih ⊢
    rw [ih,pow_succ]
    ring
end ThreeSum.TernarySignedDigits
