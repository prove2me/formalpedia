-- Prove2me | solution 1 for SmallRatio.err_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:36:59.83581+00:00
-- url     : https://prove2.me/submissions/d785c9ec-5773-4ec1-b720-b6e8cba8fa86

module
public import Definitions.Def_SmallRatio_Reciprocity
public import Definitions.Def_SmallRatio_Euclid
public import Definitions.Def_SmallRatio_AlongEuclid
public import Theorems.Thm_SmallRatio_den_mono
public import Theorems.Thm_SmallRatio_den_pos
public import Theorems.Thm_SmallRatio_pos_rem_of_le_steps
public import Theorems.Thm_SmallRatio_rem_succ_lt


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {k h : ℕ} (hh : 0 < h) (hhk : h < k) (hc : Nat.Coprime k h)
include hh hhk hc
namespace SmallRatio
theorem _root_.solution {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ steps k h) :
    |(-(den k h (i - 1) : ℚ) / den k h i + (rem k h i : ℚ) / rem k h (i - 1)
        + 1 / ((rem k h i : ℚ) * rem k h (i - 1)) - 3)| ≤ 4 := by
  have hr := pos_rem_of_le_steps hh hhk hc hi
  have hlt := rem_succ_lt hh hhk hc (show i - 1 < steps k h by omega)
  rw [show i - 1 + 1 = i by omega] at hlt
  have hd := den_pos hh hhk hc hi1 (by omega)
  have hmono := den_mono hh hhk hc (show i - 1 ≤ steps k h by omega)
  rw [show i - 1 + 1 = i by omega] at hmono
  have hrq : (0 : ℚ) < rem k h i := by exact_mod_cast hr
  have hlq : (rem k h i : ℚ) < rem k h (i - 1) := by exact_mod_cast hlt
  have hdq : (1 : ℚ) ≤ den k h i := by exact_mod_cast hd
  have hmq : (den k h (i - 1) : ℚ) ≤ den k h i := by exact_mod_cast hmono
  have hd0 : (0 : ℚ) ≤ den k h (i - 1) := by positivity
  have a1 : (den k h (i - 1) : ℚ) / den k h i ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hmq
  have a2 : 0 ≤ (den k h (i - 1) : ℚ) / den k h i := by positivity
  have a3 : (rem k h i : ℚ) / rem k h (i - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hlq.le
  have a4 : 0 ≤ (rem k h i : ℚ) / rem k h (i - 1) := by positivity
  have hprod : (1 : ℚ) ≤ (rem k h i : ℚ) * rem k h (i - 1) := by
    have : (1 : ℚ) ≤ rem k h i := by exact_mod_cast hr
    nlinarith
  have a5 : 1 / ((rem k h i : ℚ) * rem k h (i - 1)) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hprod
  have a6 : 0 ≤ 1 / ((rem k h i : ℚ) * rem k h (i - 1)) := by positivity
  rw [abs_le]
  constructor
  · rw [neg_div]; linarith
  · rw [neg_div]; linarith
end SmallRatio
