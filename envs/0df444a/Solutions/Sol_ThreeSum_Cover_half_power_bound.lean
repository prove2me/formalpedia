-- Prove2me | solution 1 for ThreeSum.Cover.half_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:09:17.781194+00:00
-- url     : https://prove2.me/submissions/4571d801-181e-44b4-aa4c-71ae903b031f

import Definitions.Def_Submission_ThreeSum_Cover
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Aesop
import Definitions.Def_Submission_ThreeSum_Greedy

set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators
variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]
namespace ThreeSum.Cover
theorem _root_.solution (a : ℕ) (ha : 0 < a) : 2 * (a - 1) ^ a ≤ a ^ a := by
  have hae : a - 1 + 1 = a := by omega
  have h := pow_add_mul_le_add_pow (a := a - 1) (b := 1)
    (Nat.zero_le _) (Nat.zero_le _) a
  simp only [hae, mul_one] at h
  have hpow : (a - 1) ^ a = (a - 1) ^ (a - 1) * (a - 1) := by
    calc
      (a - 1) ^ a = (a - 1) ^ ((a - 1) + 1) := congrArg ((a - 1) ^ ·) hae.symm
      _ = (a - 1) ^ (a - 1) * (a - 1) := pow_succ _ _
  have hm := Nat.mul_le_mul_left ((a - 1) ^ (a - 1)) (Nat.sub_le a 1)
  nlinarith
end ThreeSum.Cover
