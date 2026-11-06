-- Prove2me | solution 1 for ThmCount.time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:13:24.565675+00:00
-- url     : https://prove2.me/submissions/0544d0cd-316a-45c3-b991-23f387163f8b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Tactic
import Definitions.Def_ThmCount_Rates
import Theorems.Thm_ThmCount_natCast_le_two_rpow
import Theorems.Thm_VariableBound_Paper_natCast_le_two_rpow
import Theorems.Thm_Wrap_Arith_pow_le_rate
import Theorems.Thm_Wrap_Arith_rate_eq
import Theorems.Thm_Wrap_Arith_rate_le_eight
import Theorems.Thm_Wrap_Arith_rate_nonneg


set_option autoImplicit false
section
section
open ThmCount
namespace ThmCount
theorem _root_.solution (C q a d : ℕ) : ∃ K : ℝ, ∀ (n : ℕ) (R : ℝ), (n : ℝ) * SatK.rN 1 (1 / 2) n ≤ 8 * R → 1 ≤ R →
    (q : ℝ) * ((2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN 3 (n + 4)) + (a : ℝ) * ((n : ℝ) + 2) ^ d + 1) ^ q ≤ (2 : ℝ) ^ (K * R) := by
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = (q : ℝ) * (9 * C + 64 * d) := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℝ, c₂ = (q : ℝ) * (288 * C + 256 * d + a + 3) := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
  refine ⟨8 * c₁ + c₂, fun n R hR h1 => ?_⟩
  obtain ⟨r, hr⟩ : ∃ r, r = SatK.rN 1 (1 / 2) n := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := hr ▸ Wrap.Arith.rate_nonneg n
  have hr8 : r ≤ 8 := hr ▸ Wrap.Arith.rate_le_eight n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hexp : MainTheoremForms.expN 3 (n + 4) = 9 * (((n : ℝ) + 4) * r) := by
    rw [hr, Wrap.Arith.rate_eq]
    unfold MainTheoremForms.expN
    push_cast
    ring
  have p1 := Wrap.Arith.pow_le_rate d n
  rw [← hr] at hR p1
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (n : ℝ) * r := ⟨_, rfl⟩
  rw [← hρ] at hR p1
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hexp' : MainTheoremForms.expN 3 (n + 4) ≤ 9 * ρ + 288 := by rw [hexp, hρ]; linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = C * (9 * ρ + 288) + d * (64 * ρ + 256) + a := ⟨_, rfl⟩
  have t1 : (0 : ℝ) ≤ C * (9 * ρ + 288) := by positivity
  have t2 : (0 : ℝ) ≤ d * (64 * ρ + 256) := by positivity
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℝ, X₁ = (2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN 3 (n + 4)) := ⟨_, rfl⟩
  obtain ⟨X₂, hX₂⟩ : ∃ X₂ : ℝ, X₂ = (a : ℝ) * ((n : ℝ) + 2) ^ d := ⟨_, rfl⟩
  rw [← hX₁, ← hX₂]
  have hX₁0 : 0 ≤ X₁ := by rw [hX₁]; positivity
  have hX₂0 : 0 ≤ X₂ := by rw [hX₂]; positivity
  have x1 : X₁ ≤ (2 : ℝ) ^ B := by
    rw [hX₁]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    have := mul_le_mul_of_nonneg_left hexp' hC0
    rw [hB]
    linarith
  have x2 : X₂ ≤ (2 : ℝ) ^ B := by
    rw [hX₂]
    calc (a : ℝ) * ((n : ℝ) + 2) ^ d ≤ (2 : ℝ) ^ (a : ℝ) * (2 : ℝ) ^ ((d : ℝ) * (64 * ρ + 256)) :=
          mul_le_mul (natCast_le_two_rpow a) p1 (by positivity) (by positivity)
      _ = (2 : ℝ) ^ ((a : ℝ) + (d : ℝ) * (64 * ρ + 256)) := (Real.rpow_add two_pos _ _).symm
      _ ≤ (2 : ℝ) ^ B := Real.rpow_le_rpow_of_exponent_le one_le_two (by rw [hB]; linarith)
  have x3 : (1 : ℝ) ≤ (2 : ℝ) ^ B := Real.one_le_rpow one_le_two hB0
  have e4 : (2 : ℝ) ^ (B + 2) = (2 : ℝ) ^ B * 4 := by
    rw [Real.rpow_add two_pos, Real.rpow_two]
    norm_num
  have hsum : X₁ + X₂ + 1 ≤ (2 : ℝ) ^ (B + 2) := by rw [e4]; linarith
  have hpow : (X₁ + X₂ + 1) ^ q ≤ (2 : ℝ) ^ ((B + 2) * q) := by
    rw [Real.rpow_mul_natCast two_pos.le]
    exact pow_le_pow_left₀ (by positivity) hsum q
  calc (q : ℝ) * (X₁ + X₂ + 1) ^ q ≤ (2 : ℝ) ^ (q : ℝ) * (2 : ℝ) ^ ((B + 2) * q) :=
        mul_le_mul (natCast_le_two_rpow q) hpow (by positivity) (by positivity)
    _ = (2 : ℝ) ^ ((q : ℝ) + (B + 2) * q) := (Real.rpow_add two_pos _ _).symm
    _ ≤ (2 : ℝ) ^ ((8 * c₁ + c₂) * R) := by
        refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
        have e : (q : ℝ) + (B + 2) * q = c₁ * ρ + c₂ := by rw [hB, hc₁, hc₂]; ring
        have u1 : c₁ * ρ ≤ c₁ * (8 * R) := mul_le_mul_of_nonneg_left hR hc₁0
        have u2 : c₂ ≤ c₂ * R := le_mul_of_one_le_right hc₂0 h1
        have u3 : (8 * c₁ + c₂) * R = c₁ * (8 * R) + c₂ * R := by ring
        rw [e, u3]
        linarith
end ThmCount
