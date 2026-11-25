-- Prove2me | solution 1 for SmallRatio.y_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:25.172002+00:00
-- url     : https://prove2.me/submissions/7b45d9bc-027a-447c-90f6-dc9838f27574

module
public import Definitions.Def_SmallRatio_Euclid
public import Definitions.Def_SmallRatio_Legendre
public import Theorems.Thm_SmallRatio_rem_den_identity


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution {j : ℕ} (hj : j ≤ steps k h) :
    (rem k h j : ℤ) * ((-1) ^ (j + 2) * den k h (j + 1)) -
      (rem k h (j + 1) : ℤ) * ((-1) ^ (j + 1) * den k h j) = (-1) ^ j * k := by
  have e := rem_den_identity hh hhk hc hj
  have e' : (rem k h j : ℤ) * den k h (j + 1) + (rem k h (j + 1) : ℤ) * den k h j = k := by
    exact_mod_cast e
  rw [← e']
  ring
end SmallRatio
