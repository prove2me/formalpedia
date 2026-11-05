-- Prove2me | solution 1 for Wrap.Arith.rate_le_const_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:55:06.996561+00:00
-- url     : https://prove2.me/submissions/762da4c5-44a8-47a3-a425-5f27741889b3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Wrap_Arith
import Theorems.Thm_Wrap_Arith_lg_div_sqrt_le
import Theorems.Thm_VariableBound_Paper_lg_add_four


set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) {n₀ : ℕ} (hn₀ : (2 : ℝ) ^ ((8 * B / ε) ^ 4) ≤ n₀) {n : ℕ} (hn : 4 ≤ n) :
    B * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)) ≤ 8 * B * n₀ + ε * n := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  obtain ⟨hy, -, hyy, -, -⟩ := VariableBound.Paper.lg_add_four hn
  have hy0 : 0 < lg n := by linarith
  have hw1 : 1 ≤ Real.sqrt (Real.sqrt (lg n)) := Real.one_le_sqrt.2 (Real.one_le_sqrt.2 (by linarith))
  have hw0 : 0 < Real.sqrt (Real.sqrt (lg n)) := by linarith
  have hg := lg_div_sqrt_le hy0
  have hg0 : 0 ≤ lg (lg n) / Real.sqrt (lg n) := div_nonneg (by linarith) (Real.sqrt_nonneg _)
  rw [mul_div_assoc]
  rcases le_total n n₀ with hle | hle
  · have hle' : (n : ℝ) ≤ n₀ := by exact_mod_cast hle
    have hg8 : lg (lg n) / Real.sqrt (lg n) ≤ 8 := hg.trans (div_le_self (by norm_num) hw1)
    have h1 : (n : ℝ) * (lg (lg n) / Real.sqrt (lg n)) ≤ n₀ * 8 := mul_le_mul hle' hg8 hg0 (Nat.cast_nonneg n₀)
    have h2 := mul_le_mul_of_nonneg_left h1 hB
    have h3 : 0 ≤ ε * n := mul_nonneg hε.le hn0
    linarith
  · have hle' : (n₀ : ℝ) ≤ n := by exact_mod_cast hle
    have ha : (8 * B / ε) ^ 4 ≤ lg n := by
      unfold lg
      rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith)]
      exact hn₀.trans hle'
    have haw : 8 * B / ε ≤ Real.sqrt (Real.sqrt (lg n)) := by
      apply Real.le_sqrt_of_sq_le
      apply Real.le_sqrt_of_sq_le
      calc ((8 * B / ε) ^ 2) ^ 2 = (8 * B / ε) ^ 4 := by ring
        _ ≤ lg n := ha
    have h1 : B * (lg (lg n) / Real.sqrt (lg n)) ≤ ε := by
      calc B * (lg (lg n) / Real.sqrt (lg n)) ≤ B * (8 / Real.sqrt (Real.sqrt (lg n))) := mul_le_mul_of_nonneg_left hg hB
        _ = 8 * B / Real.sqrt (Real.sqrt (lg n)) := by ring
        _ ≤ ε := by
          rw [div_le_iff₀ hw0]
          rw [div_le_iff₀ hε] at haw
          linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hn0
    have h3 : 0 ≤ 8 * B * n₀ := mul_nonneg (mul_nonneg (by norm_num) hB) (Nat.cast_nonneg n₀)
    calc B * ((n : ℝ) * (lg (lg n) / Real.sqrt (lg n))) = n * (B * (lg (lg n) / Real.sqrt (lg n))) := by ring
      _ ≤ n * ε := h2
      _ ≤ 8 * B * n₀ + ε * n := by linarith
end Wrap.Arith
