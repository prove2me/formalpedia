-- Prove2me | solution 1 for SmallRatio.den_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:35:27.602134+00:00
-- url     : https://prove2.me/submissions/2e33b4ef-60b4-4e7d-8080-994572081dba

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
theorem _root_.solution {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ steps k h + 1) : 1 ≤ den k h j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => omega
    | 1, _ => simp
    | j + 2, ih =>
      have h1 := ih (j + 1) (by omega) (by omega) (by omega)
      have ha := rem_div_rem_pos hh hhk hc (show j < steps k h by omega)
      rw [den_add_two]
      nlinarith
end SmallRatio
