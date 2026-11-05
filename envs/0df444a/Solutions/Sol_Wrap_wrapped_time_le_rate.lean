-- Prove2me | solution 1 for Wrap.wrapped_time_le_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:59:08.780449+00:00
-- url     : https://prove2.me/submissions/4c894ac5-40b0-42f7-9b91-33ea239b654e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_Wrap_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_Wrap_ArithRate
import Theorems.Thm_Wrap_Arith_rate_nonneg
import Theorems.Thm_Wrap_Arith_rate_le_eight
import Theorems.Thm_Wrap_Arith_exponent_le
import Theorems.Thm_Wrap_Arith_pow_le_rate
import Theorems.Thm_Wrap_Arith_poly_part_le
import Theorems.Thm_Wrap_Arith_timeMin3_le


set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Arith
namespace Wrap
theorem _root_.solution (q C₁ C₂ a d : ℕ) :
    ∃ c : ℕ, ∀ (n m' n' L X : ℕ), 2 ≤ m' → 4 ≤ n' → n' ≤ n + 4 → L ≤ a * (n + 2) ^ d → X ≤ a * (n + 2) ^ d →
      q * ((MainTheoremForms.timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1) ^ q ≤ SatM.boundNK (SatK.rN 1 (1 / 2)) c 3 n := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = d * C₂ + d := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = C₂ * a ^ C₂ + a + 1 := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, κ = C₁ + 64 * D := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 : ℝ) ^ ((C₁ : ℝ) * 32) + (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * 256) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨c₀, hc₀⟩ := exists_nat_ge ((q : ℝ) * K ^ q)
  refine ⟨c₀ + κ * q, fun n m' n' L X _ hn' hnn hL hX => Nat.le_floor ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (n : ℝ) * SatK.rN 1 (1 / 2) n := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; exact mul_nonneg hn0 (rate_nonneg n)
  have hC₁κ : (C₁ : ℝ) ≤ κ := by rw [hκ]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) D]
  have hDκ : (D : ℝ) * 64 ≤ κ := by rw [hκ]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) C₁]
  have hT : (timeMin3 C₁ m' n' : ℝ) ≤ (2 : ℝ) ^ ((C₁ : ℝ) * 32) * (2 : ℝ) ^ ((κ : ℝ) * E) := by
    have h1 : (n' : ℝ) * lg (lg n') / Real.sqrt (lg n') ≤ 32 + E := by
      have h2 := exponent_le hn' hnn
      have h3 := rate_le_eight n
      rw [hE]
      linarith
    calc (timeMin3 C₁ m' n' : ℝ) ≤ (2 : ℝ) ^ ((C₁ : ℝ) * ((n' : ℝ) * lg (lg n') / Real.sqrt (lg n'))) := timeMin3_le C₁ m' n'
      _ ≤ (2 : ℝ) ^ ((C₁ : ℝ) * (32 + E)) := Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg C₁))
      _ = (2 : ℝ) ^ ((C₁ : ℝ) * 32) * (2 : ℝ) ^ ((C₁ : ℝ) * E) := by rw [mul_add, Real.rpow_add two_pos]
      _ ≤ (2 : ℝ) ^ ((C₁ : ℝ) * 32) * (2 : ℝ) ^ ((κ : ℝ) * E) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hC₁κ hE0)) (Real.rpow_nonneg zero_le_two _)
  have hQ : ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) ≤ (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((κ : ℝ) * E) := by
    calc ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) ≤ ((A * (n + 2) ^ D : ℕ) : ℝ) := by
          rw [hA, hD]
          exact_mod_cast poly_part_le C₂ a d hL hX
      _ = (A : ℝ) * ((n : ℝ) + 2) ^ D := by push_cast; ring
      _ ≤ (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * (64 * E + 256)) := by
          rw [hE]
          exact mul_le_mul_of_nonneg_left (pow_le_rate D n) (Nat.cast_nonneg A)
      _ = (A : ℝ) * ((2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((D : ℝ) * 64 * E)) := by
          rw [← Real.rpow_add two_pos]
          congr 2
          ring
      _ ≤ (A : ℝ) * ((2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((κ : ℝ) * E)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hDκ hE0))
            (Real.rpow_nonneg zero_le_two _)) (Nat.cast_nonneg A)
      _ = (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((κ : ℝ) * E) := by ring
  have hb : (((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) ≤ K * (2 : ℝ) ^ ((κ : ℝ) * E) := by
    have e1 : (((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) = (timeMin3 C₁ m' n' : ℝ) + ((C₂ * L ^ C₂ + X + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have e2 : K * (2 : ℝ) ^ ((κ : ℝ) * E) = (2 : ℝ) ^ ((C₁ : ℝ) * 32) * (2 : ℝ) ^ ((κ : ℝ) * E) + (A : ℝ) * (2 : ℝ) ^ ((D : ℝ) * 256) * (2 : ℝ) ^ ((κ : ℝ) * E) := by
      rw [hK]
      ring
    rw [e1, e2]
    exact add_le_add hT hQ
  have hc₀' : (q : ℝ) * K ^ q ≤ ((c₀ + κ * q : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ (κ : ℝ) * q := by positivity
    linarith
  have hpow : ((2 : ℝ) ^ ((κ : ℝ) * E)) ^ q ≤ (2 : ℝ) ^ (((c₀ + κ * q : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    have e3 : ((c₀ + κ * q : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n = (((c₀ : ℝ) + (κ : ℝ) * q) * 9) * E := by
      rw [hE]
      push_cast
      ring
    rw [e3]
    have h7 : (κ : ℝ) * q ≤ ((c₀ : ℝ) + (κ : ℝ) * q) * 9 := by
      have h8 : (0 : ℝ) ≤ (κ : ℝ) * q := by positivity
      have h9 : (0 : ℝ) ≤ (c₀ : ℝ) := Nat.cast_nonneg c₀
      linarith
    calc (κ : ℝ) * E * q = (κ : ℝ) * q * E := by ring
      _ ≤ ((c₀ : ℝ) + (κ : ℝ) * q) * 9 * E := mul_le_mul_of_nonneg_right h7 hE0
  calc ((q * ((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1) ^ q : ℕ) : ℝ)
        = (q : ℝ) * (((timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1 : ℕ) : ℝ) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (K * (2 : ℝ) ^ ((κ : ℝ) * E)) ^ q := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hb q) (Nat.cast_nonneg q)
    _ = (q : ℝ) * K ^ q * ((2 : ℝ) ^ ((κ : ℝ) * E)) ^ q := by rw [mul_pow]; ring
    _ ≤ ((c₀ + κ * q : ℕ) : ℝ) * (2 : ℝ) ^ (((c₀ + κ * q : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n) :=
        mul_le_mul hc₀' hpow (by positivity) (Nat.cast_nonneg _)
end Wrap
