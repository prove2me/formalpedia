-- Prove2me | solution 1 for SmallRatio.telescope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:32:34.528485+00:00
-- url     : https://prove2.me/submissions/82e76e5b-6fdc-4b39-848d-d10b04440f6b

module
public import Definitions.Def_SmallRatio_Reciprocity
public import Definitions.Def_SmallRatio_Euclid
public import Definitions.Def_SmallRatio_AlongEuclid
public import Theorems.Thm_SmallRatio_dedekindSum_mod
public import Theorems.Thm_SmallRatio_dedekind_reciprocity
public import Theorems.Thm_SmallRatio_den_one
public import Theorems.Thm_SmallRatio_den_zero
public import Theorems.Thm_SmallRatio_gcd_rem
public import Theorems.Thm_SmallRatio_pos_rem_of_le_steps
public import Theorems.Thm_SmallRatio_rem_add_two
public import Theorems.Thm_SmallRatio_rem_one
public import Theorems.Thm_SmallRatio_rem_zero
attribute [local simp] SmallRatio.den_one
attribute [local simp] SmallRatio.den_zero
attribute [local simp] SmallRatio.rem_one
attribute [local simp] SmallRatio.rem_zero



set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution {j : ℕ} (hj : j ≤ steps k h) :
    12 * dedekindSum h k = ∑ i ∈ Ico 1 (j + 1), (-1) ^ (i + 1) * recipTerm k h i
      + (-1) ^ j * (12 * dedekindSum (rem k h (j + 1)) (rem k h j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih (by omega), sum_Ico_succ_top (a := 1) (b := j + 1) (by omega)]
    have h0 := pos_rem_of_le_steps hh hhk hc (show j ≤ steps k h by omega)
    have h1 := pos_rem_of_le_steps hh hhk hc hj
    have hg := gcd_rem (k := k) (h := h) j
    rw [hc] at hg
    have hrec := dedekind_reciprocity (rem k h (j + 1)) (rem k h j) h1 h0
      (by rw [Nat.Coprime, Nat.gcd_comm]; exact hg)
    have hmod := dedekindSum_mod (rem k h j) (rem k h (j + 1)) h1
    rw [← rem_add_two] at hmod
    have hR : recipTerm k h (j + 1) = 12 * (dedekindSum (rem k h (j + 1)) (rem k h j) +
        dedekindSum (rem k h j) (rem k h (j + 1))) := by
      rw [hrec]
      unfold recipTerm
      simp only [Nat.add_sub_cancel]
      have : (rem k h j : ℚ) ≠ 0 := by exact_mod_cast h0.ne'
      have : (rem k h (j + 1) : ℚ) ≠ 0 := by exact_mod_cast h1.ne'
      field_simp
      ring
    rw [show j + 1 + 1 = j + 2 by ring, ← hmod, hR]
    ring
end SmallRatio
