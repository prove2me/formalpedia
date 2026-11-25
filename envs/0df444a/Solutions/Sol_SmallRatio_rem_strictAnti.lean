-- Prove2me | solution 1 for SmallRatio.rem_strictAnti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:12.080318+00:00
-- url     : https://prove2.me/submissions/c60f4734-64d2-4929-9c17-116d07b1aa6f

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_succ_lt

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution {i j : ℕ} (hij : i < j) (hj : j ≤ steps k h) : rem k h j < rem k h i := by
  induction j with
  | zero => omega
  | succ j ih =>
    have h1 := rem_succ_lt hh hhk hc (show j < steps k h by omega)
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hij) with h2 | h2
    · exact lt_trans h1 (ih h2 (by omega))
    · subst h2; exact h1
end SmallRatio
