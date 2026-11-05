-- Prove2me | solution 1 for Wrap.wrapped_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:57:20.209491+00:00
-- url     : https://prove2.me/submissions/ffd7f380-b300-4ed4-ac71-c23ce1a50fc2

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
import Theorems.Thm_Wrap_Arith_rate_below
import Theorems.Thm_Wrap_Arith_timeMin3_le
import Theorems.Thm_Wrap_Arith_poly_below
import Theorems.Thm_Wrap_Arith_poly_part_le

set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Arith
namespace Wrap
theorem _root_.solution (q C₁ C₂ a d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℕ, ∀ (n m' n' L X : ℕ), 2 ≤ m' → 4 ≤ n' → n' ≤ n + 4 → L ≤ a * (n + 2) ^ d → X ≤ a * (n + 2) ^ d →
      q * ((MainTheoremForms.timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1) ^ q ≤ ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = δ / ((q : ℝ) + 1) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; exact div_pos hδ hq1
  have hεq : ε * q ≤ δ := by
    rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ hq1]
    nlinarith
  obtain ⟨c₁, hc₁⟩ := rate_below (Nat.cast_nonneg C₁) hε
  obtain ⟨c₂, hc₂⟩ := poly_below (d * C₂ + d) hε
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = C₂ * a ^ C₂ + a + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (c₁ : ℝ) * (2 : ℝ) ^ (ε * 4) + (A : ℝ) * c₂ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨c, hc⟩ := exists_nat_ge ((q : ℝ) * K ^ q)
  refine ⟨c, fun n m' n' L X _ hn' hnn hL hX => Nat.le_floor ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hT : (timeMin3 C₁ m' n' : ℝ) ≤ (c₁ : ℝ) * (2 : ℝ) ^ (ε * 4) * (2 : ℝ) ^ (ε * n) := by
    have hnn' : (n' : ℝ) ≤ (n : ℝ) + 4 := by exact_mod_cast hnn
    calc (timeMin3 C₁ m' n' : ℝ) ≤ (2 : ℝ) ^ ((C₁ : ℝ) * ((n' : ℝ) * lg (lg n') / Real.sqrt (lg n'))) := timeMin3_le C₁ m' n'
      _ ≤ (c₁ : ℝ) * (2 : ℝ) ^ (ε * n') := hc₁ n' hn'
      _ ≤ (c₁ : ℝ) * (2 : ℝ) ^ (ε * ((n : ℝ) + 4)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hnn' hε.le)) (Nat.cast_nonneg c₁)
      _ = (c₁ : ℝ) * (2 : ℝ) ^ (ε * 4) * (2 : ℝ) ^ (ε * n) := by
          rw [mul_add, Real.rpow_add two_pos]
          ring
  have hQ : ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) ≤ (A : ℝ) * c₂ * (2 : ℝ) ^ (ε * n) := by
    calc ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) ≤ ((A * (n + 2) ^ (d * C₂ + d) : ℕ) : ℝ) := by
          rw [hA]
          exact_mod_cast poly_part_le C₂ a d hL hX
      _ = (A : ℝ) * ((n : ℝ) + 2) ^ (d * C₂ + d) := by push_cast; ring
      _ ≤ (A : ℝ) * ((c₂ : ℝ) * (2 : ℝ) ^ (ε * n)) := mul_le_mul_of_nonneg_left (hc₂ n) (Nat.cast_nonneg A)
      _ = (A : ℝ) * c₂ * (2 : ℝ) ^ (ε * n) := by ring
  have hb : (((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) ≤ K * (2 : ℝ) ^ (ε * n) := by
    have e1 : (((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) = (timeMin3 C₁ m' n' : ℝ) + ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have e2 : K * (2 : ℝ) ^ (ε * n) = (c₁ : ℝ) * (2 : ℝ) ^ (ε * 4) * (2 : ℝ) ^ (ε * n) + (A : ℝ) * c₂ * (2 : ℝ) ^ (ε * n) := by
      rw [hK]
      ring
    rw [e1, e2]
    exact add_le_add hT hQ
  have hpow : ((2 : ℝ) ^ (ε * n)) ^ q ≤ (2 : ℝ) ^ (δ * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    calc ε * n * q = ε * q * n := by ring
      _ ≤ δ * n := mul_le_mul_of_nonneg_right hεq hn0
  calc ((q * ((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1) ^ q : ℕ) : ℝ)
        = (q : ℝ) * (((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (K * (2 : ℝ) ^ (ε * n)) ^ q := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hb q) (Nat.cast_nonneg q)
    _ = (q : ℝ) * K ^ q * ((2 : ℝ) ^ (ε * n)) ^ q := by rw [mul_pow]; ring
    _ ≤ (q : ℝ) * K ^ q * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ (c : ℝ) * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg zero_le_two _)
end Wrap
