-- Prove2me | solution 1 for RamanujanNested.altSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-27T05:06:09.676887+00:00
-- url     : https://prove2.me/submissions/04addaeb-bf7f-405c-aff3-18448a489597

module
public import Mathlib
public import Definitions.Def_RamanujanNested_IdentityChainNthRoot
public import Theorems.Thm_RamanujanNested_altSum_identity

set_option autoImplicit true
@[expose] public section
open RamanujanNested
open Finset
namespace RamanujanNested
theorem _root_.solution {n : ℕ} {x : ℝ} (hx : 1 ≤ x) : 0 ≤ altSum n x := by
  have hid := altSum_identity n x
  have hxp1_pos : (0 : ℝ) < x + 1 := by linarith
  have h1 : (-1 : ℝ) ^ n ≤ 1 := by
    have habs : |(-1 : ℝ) ^ n| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
    have hle := le_abs_self ((-1 : ℝ) ^ n)
    linarith [habs ▸ hle]
  have hxn_ge1 : (1 : ℝ) ≤ x ^ n := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx n
    rwa [one_pow] at h
  have hxn_sub_nonneg : (0 : ℝ) ≤ x ^ n - (-1 : ℝ) ^ n := by linarith
  have hval : altSum n x = (x ^ n - (-1 : ℝ) ^ n) / (x + 1) :=
    (eq_div_iff (ne_of_gt hxp1_pos)).mpr hid
  rw [hval]
  exact div_nonneg hxn_sub_nonneg hxp1_pos.le
end RamanujanNested
