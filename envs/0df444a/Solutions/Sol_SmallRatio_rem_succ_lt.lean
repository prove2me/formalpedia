-- Prove2me | solution 1 for SmallRatio.rem_succ_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:32:31.029947+00:00
-- url     : https://prove2.me/submissions/c62d2853-799c-4fbd-bc87-45a344b062f2

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_zero
public import Theorems.Thm_SmallRatio_rem_one
public import Theorems.Thm_SmallRatio_rem_add_two
public import Theorems.Thm_SmallRatio_den_zero
public import Theorems.Thm_SmallRatio_den_one
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
theorem _root_.solution {j : ℕ} (hj : j < steps k h) : rem k h (j + 1) < rem k h j := by
  cases j with
  | zero => simpa using hhk
  | succ j =>
    rw [rem_add_two]
    exact Nat.mod_lt _ (pos_rem_of_le_steps hh hhk hc (by omega))
end SmallRatio
