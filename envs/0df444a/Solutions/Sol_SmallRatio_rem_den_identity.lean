-- Prove2me | solution 1 for SmallRatio.rem_den_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:32:28.764233+00:00
-- url     : https://prove2.me/submissions/72f47d87-aec0-4e48-8d59-49a02e29302b

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_zero
public import Theorems.Thm_SmallRatio_rem_one
public import Theorems.Thm_SmallRatio_rem_add_two
public import Theorems.Thm_SmallRatio_den_zero
public import Theorems.Thm_SmallRatio_den_one
public import Theorems.Thm_SmallRatio_den_add_two
public import Theorems.Thm_SmallRatio_pos_rem_of_le_steps
attribute [local simp] SmallRatio.rem_zero
attribute [local simp] SmallRatio.rem_one
attribute [local simp] SmallRatio.den_zero
attribute [local simp] SmallRatio.den_one

set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ}
variable (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution {j : ℕ} (hj : j ≤ steps k h) :
    rem k h j * den k h (j + 1) + rem k h (j + 1) * den k h j = k := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ih := ih (by omega)
    have hp := pos_rem_of_le_steps hh hhk hc hj
    have hmod := Nat.mod_add_div (rem k h j) (rem k h (j + 1))
    rw [den_add_two, rem_add_two]
    calc rem k h (j + 1) * (rem k h j / rem k h (j + 1) * den k h (j + 1) + den k h j) +
          rem k h j % rem k h (j + 1) * den k h (j + 1)
        = (rem k h j % rem k h (j + 1) + rem k h (j + 1) * (rem k h j / rem k h (j + 1))) *
            den k h (j + 1) + rem k h (j + 1) * den k h j := by ring
      _ = k := by rw [hmod]; exact ih
end SmallRatio
