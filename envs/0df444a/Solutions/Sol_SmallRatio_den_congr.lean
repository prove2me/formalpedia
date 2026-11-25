-- Prove2me | solution 1 for SmallRatio.den_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:19:55.679907+00:00
-- url     : https://prove2.me/submissions/55518ff6-3a69-4e2c-9b31-392e87c01069

module
public import Definitions.Def_SmallRatio_Defs
public import Definitions.Def_SmallRatio_Euclid
public import Theorems.Thm_SmallRatio_rem_zero
public import Theorems.Thm_SmallRatio_rem_one
public import Theorems.Thm_SmallRatio_rem_add_two
public import Theorems.Thm_SmallRatio_den_zero
public import Theorems.Thm_SmallRatio_den_one
public import Theorems.Thm_SmallRatio_den_add_two
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
omit hh hhk hc
namespace SmallRatio
theorem _root_.solution (j : ℕ) :
    (k : ℤ) ∣ (h : ℤ) * den k h j - (-1) ^ (j + 1) * rem k h j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => exact ⟨1, by simp⟩
    | 1, _ => exact ⟨0, by simp⟩
    | j + 2, ih =>
      have h0 := ih j (by omega)
      have h1 := ih (j + 1) (by omega)
      have hmod := Nat.mod_add_div (rem k h j) (rem k h (j + 1))
      set a := rem k h j / rem k h (j + 1)
      have hmodZ : ((rem k h j % rem k h (j + 1) : ℕ) : ℤ) =
          (rem k h j : ℤ) - (rem k h (j + 1) : ℤ) * a := by
        have : ((rem k h j % rem k h (j + 1) : ℕ) : ℤ) + (rem k h (j + 1) : ℤ) * a =
            (rem k h j : ℤ) := by exact_mod_cast hmod
        linarith
      rw [den_add_two, rem_add_two, Nat.cast_add, Nat.cast_mul, hmodZ]
      have e : (h : ℤ) * (a * den k h (j + 1) + den k h j) - (-1) ^ (j + 2 + 1) *
          ((rem k h j : ℤ) - rem k h (j + 1) * a) =
          a * ((h : ℤ) * den k h (j + 1) - (-1) ^ (j + 1 + 1) * rem k h (j + 1)) +
          ((h : ℤ) * den k h j - (-1) ^ (j + 1) * rem k h j) := by ring
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_right h1 _) h0
end SmallRatio
