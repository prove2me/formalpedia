-- Prove2me | solution 1 for ThmCount.remark_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:18:32.927677+00:00
-- url     : https://prove2.me/submissions/903cfaa3-5f53-4268-b673-887b5818ed73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Tactic
import Definitions.Def_ThmCount_Rates
import Theorems.Thm_ThmCount_one_le_logb
import Theorems.Thm_ThmCount_rate_le
import Theorems.Thm_Sat3_one_le_logb


set_option autoImplicit false
section
section
open ThmCount
namespace ThmCount
theorem _root_.solution {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) * SatK.rN 1 (1 / 2) n ≤ 8 * ((n : ℝ) * Real.logb 2 (Real.logb 2 n) ^ ((2 : ℝ) / 3) / Real.logb 2 n ^ ((1 : ℝ) / 6)) ∧
      1 ≤ (n : ℝ) * Real.logb 2 (Real.logb 2 n) ^ ((2 : ℝ) / 3) / Real.logb 2 n ^ ((1 : ℝ) / 6) := by
  obtain ⟨h1, h2⟩ := rate_le (n := n) (by omega) (e := (1 : ℝ) / 6) (by norm_num)
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hx2 : 2 ≤ Real.logb 2 (n : ℝ) := by
    have h := Real.logb_le_logb_of_le one_lt_two (by norm_num : (0 : ℝ) < 4) hn4
    have e : Real.logb 2 (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
      norm_num
    rwa [e] at h
  have hy : 1 ≤ Real.logb 2 (Real.logb 2 (n : ℝ)) ^ ((2 : ℝ) / 3) := Real.one_le_rpow (one_le_logb hx2) (by norm_num)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Real.logb 2 (Real.logb 2 (n : ℝ)) ^ ((2 : ℝ) / 3) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = (n : ℝ) / Real.logb 2 n ^ ((1 : ℝ) / 6) := ⟨_, rfl⟩
  rw [← hY] at hy ⊢
  rw [← hR] at h1 h2
  have e : (n : ℝ) * Y / Real.logb 2 n ^ ((1 : ℝ) / 6) = R * Y := by rw [hR]; ring
  rw [e]
  have hRY : R ≤ R * Y := le_mul_of_one_le_right (by linarith) hy
  exact ⟨by linarith, by linarith⟩
end ThmCount
