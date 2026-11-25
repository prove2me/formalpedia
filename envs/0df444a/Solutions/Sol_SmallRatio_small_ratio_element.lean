-- Prove2me | solution 1 for SmallRatio.small_ratio_element
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:41:38.760347+00:00
-- url     : https://prove2.me/submissions/08384437-0bf8-4fc7-8af6-128b298243b8

module
public import Definitions.Def_SmallRatio_AlongEuclid
public import Definitions.Def_SmallRatio_Legendre
public import Definitions.Def_SmallRatio_Main
public import Theorems.Thm_SmallRatio_coprime_p_h
public import Theorems.Thm_SmallRatio_small_ratio_steps
public import Theorems.Thm_SmallRatio_steps_le_log


set_option autoImplicit true
@[expose] public section
public section
open SmallRatio
open Finset
variable {p h : ℕ} (hp : p.Prime) (hh : 0 < h) (hhp : h < p)
include hp hh hhp
namespace SmallRatio
theorem _root_.solution :
    |12 * dedekindSum h p - p * smallRatioSum p h| ≤ 12 * Nat.log 2 p + 6 := by
  have hc := coprime_p_h hp hh hhp
  have h1 := small_ratio_steps hp hh hhp
  have h2 := steps_le_log hh hhp hc
  have : (6 : ℚ) * steps p h ≤ 12 * Nat.log 2 p + 6 := by
    have : (steps p h : ℚ) ≤ 2 * Nat.log 2 p + 1 := by exact_mod_cast h2
    linarith
  linarith
end SmallRatio
