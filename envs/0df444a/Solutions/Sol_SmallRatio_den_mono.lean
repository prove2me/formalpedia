-- Prove2me | solution 1 for SmallRatio.den_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:35:29.517413+00:00
-- url     : https://prove2.me/submissions/6c32a998-cc7b-4d22-bf9b-6af2a292b025

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_zero
public import Theorems.Thm_SmallRatio_rem_one
public import Theorems.Thm_SmallRatio_den_zero
public import Theorems.Thm_SmallRatio_den_one
public import Theorems.Thm_SmallRatio_den_add_two
public import Theorems.Thm_SmallRatio_rem_div_rem_pos
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
theorem _root_.solution {j : ℕ} (hj : j ≤ steps k h) : den k h j ≤ den k h (j + 1) := by
  cases j with
  | zero => simp
  | succ j =>
    have ha := rem_div_rem_pos hh hhk hc (show j < steps k h by omega)
    rw [den_add_two]
    nlinarith
end SmallRatio
