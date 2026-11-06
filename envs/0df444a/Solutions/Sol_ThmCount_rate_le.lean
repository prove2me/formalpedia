-- Prove2me | solution 1 for ThmCount.rate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:04:37.90965+00:00
-- url     : https://prove2.me/submissions/c3228b3d-1f86-47b5-a068-3a0e423e527b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Tactic
import Definitions.Def_ThmCount_Rates
import Theorems.Thm_ThmCount_sqrt_sqrt_eq
import Theorems.Thm_ThmCount_one_le_logb
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Sat3_one_le_logb
import Theorems.Thm_VariableBound_Paper_lg_le_sub_one
import Theorems.Thm_Wrap_Arith_lg_div_sqrt_le
import Theorems.Thm_Wrap_Arith_rate_eq


set_option autoImplicit false
section
section
open ThmCount
namespace ThmCount
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {e : ℝ} (he : e ≤ 1 / 4) :
    (n : ℝ) * SatK.rN 1 (1 / 2) n ≤ 8 * ((n : ℝ) / Real.logb 2 n ^ e) ∧ 1 ≤ (n : ℝ) / Real.logb 2 n ^ e := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨x, hx⟩ : ∃ x, x = Real.logb 2 (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = Real.logb 2 ((n : ℝ) + 4) := ⟨_, rfl⟩
  have hx1 : 1 ≤ x := by rw [hx]; exact one_le_logb hn2
  have hxL : x ≤ L := by rw [hx, hL]; exact Real.logb_le_logb_of_le one_lt_two hn0 (by linarith)
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos (by linarith) e
  have h1 : x ^ e ≤ Real.sqrt (Real.sqrt L) := by
    calc x ^ e ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hx1 he
      _ = Real.sqrt (Real.sqrt x) := (sqrt_sqrt_eq (by linarith)).symm
      _ ≤ Real.sqrt (Real.sqrt L) := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hxL)
  have h2 : SatK.rN 1 (1 / 2) n ≤ 8 / Real.sqrt (Real.sqrt L) := by
    have h := Wrap.Arith.lg_div_sqrt_le (y := L) (by linarith)
    rw [Wrap.Arith.rate_eq]
    rw [hL] at h ⊢
    exact h
  have h3 : 8 / Real.sqrt (Real.sqrt L) ≤ 8 / x ^ e := div_le_div_of_nonneg_left (by norm_num) hxe h1
  rw [← hx]
  constructor
  · calc (n : ℝ) * SatK.rN 1 (1 / 2) n ≤ n * (8 / x ^ e) := mul_le_mul_of_nonneg_left (h2.trans h3) hn0.le
      _ = 8 * ((n : ℝ) / x ^ e) := by ring
  · rw [one_le_div hxe]
    have h4 : Real.logb 2 (n : ℝ) ≤ (n : ℝ) - 1 := VariableBound.Paper.lg_le_sub_one (m := n) (by omega)
    calc x ^ e ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
      _ ≤ n := by rw [hx]; linarith
end ThmCount
