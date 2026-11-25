-- Prove2me | solution 1 for SmallRatio.gcd_rem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:19:30.433792+00:00
-- url     : https://prove2.me/submissions/8f778682-116d-4834-b36b-7f8855aa0cbe

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_add_two

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
namespace SmallRatio
theorem _root_.solution (j : ℕ) : Nat.gcd (rem k h j) (rem k h (j + 1)) = Nat.gcd k h := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [rem_add_two, ← ih, Nat.gcd_comm (rem k h (j + 1)), ← Nat.gcd_rec, Nat.gcd_comm]
end SmallRatio
