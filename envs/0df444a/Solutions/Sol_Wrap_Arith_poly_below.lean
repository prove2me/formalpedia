-- Prove2me | solution 1 for Wrap.Arith.poly_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:55:52.120892+00:00
-- url     : https://prove2.me/submissions/f79efec7-b880-4846-b6fe-1a668675440c

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
import Theorems.Thm_Wrap_Arith_le_two_mul_two_rpow

set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution (D : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ c : ℕ, ∀ n : ℕ, ((n : ℝ) + 2) ^ D ≤ (c : ℝ) * (2 : ℝ) ^ (ε * n) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (D : ℝ) + 1 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨c, hc⟩ := exists_nat_ge ((2 * K / ε + 2) ^ (D + 1))
  refine ⟨c, fun n => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs : 0 ≤ ε * n / K := by positivity
  have h1 := le_two_mul_two_rpow hs
  have hp1 : 1 ≤ (2 : ℝ) ^ (ε * n / K) := Real.one_le_rpow one_le_two hs
  have h2 : (n : ℝ) + 2 ≤ (2 * K / ε + 2) * (2 : ℝ) ^ (ε * n / K) := by
    have e1 : (n : ℝ) = (K / ε) * (ε * n / K) := by field_simp
    have h3 : (K / ε) * (ε * n / K) ≤ (K / ε) * (2 * (2 : ℝ) ^ (ε * n / K)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have e2 : (2 * K / ε + 2) * (2 : ℝ) ^ (ε * n / K) = (K / ε) * (2 * (2 : ℝ) ^ (ε * n / K)) + 2 * (2 : ℝ) ^ (ε * n / K) := by ring
    rw [e2]
    linarith
  calc ((n : ℝ) + 2) ^ D ≤ ((n : ℝ) + 2) ^ (D + 1) := pow_le_pow_right₀ (by linarith) (Nat.le_succ D)
    _ ≤ ((2 * K / ε + 2) * (2 : ℝ) ^ (ε * n / K)) ^ (D + 1) := pow_le_pow_left₀ (by positivity) h2 _
    _ = (2 * K / ε + 2) ^ (D + 1) * (2 : ℝ) ^ (ε * n) := by
        rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ (ε * n / K)), ← Real.rpow_mul zero_le_two]
        congr 2
        push_cast
        rw [← hK]
        field_simp
    _ ≤ (c : ℝ) * (2 : ℝ) ^ (ε * n) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg zero_le_two _)
end Wrap.Arith
