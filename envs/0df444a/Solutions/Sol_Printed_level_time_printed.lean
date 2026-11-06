-- Prove2me | solution 1 for Printed.level_time_printed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:26:15.931133+00:00
-- url     : https://prove2.me/submissions/94a4acc3-99ed-4a89-8b8d-656784e1bc6f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelNetworks
import Definitions.Def_Eight_ViaGrouping_Level
import Mathlib.Tactic
import Definitions.Def_Printed_LevelCost
import Theorems.Thm_Eight_Level_level_time
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution (g K a C₁ : ℕ) {e : ℝ} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) (Rn : ℕ) : ∃ A1 : ℕ, ∀ B lam : ℕ, 1 ≤ lam →
    (((tOf lam + 1) ^ Rn : ℕ) : ℝ) * ((((3 * C₁ : ℕ) : ℝ) + 1)
        * (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K)
        * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * lam + 1 : ℕ) : ℝ)) ^ C₁ * ((a * (B + lam) ^ a : ℕ) : ℝ)) + 2
      ≤ (A1 : ℝ) * (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ)) * ((B : ℝ) + lam) ^ A1 := by
  obtain ⟨A1, hA1⟩ := level_time g K a (3 * C₁) hK hg h0 Rn
  obtain ⟨A', hA'⟩ : ∃ A' : ℕ, A' = A1 * (g + 2) ^ A1 + A1 := ⟨_, rfl⟩
  refine ⟨A', fun B lam hl => ?_⟩
  have hg1 : 1 ≤ g := by omega
  have h := hA1 (B + g * lam + 1) lam 1 hl le_rfl
  have hX1 : 0 ≤ (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K) := by positivity
  have hX : 0 ≤ (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ)) := by positivity
  generalize (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K) = X1 at h hX1 ⊢
  generalize (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * (lam : ℝ)) = X at h hX ⊢
  have hb : g ^ 3 * lam + (g * B + g ^ 2 * lam + 1) ≤ g ^ 3 * lam + (g * (B + g * lam + 1) + g ^ 2 * tOf lam) := by
    have e1 : g * (B + g * lam + 1) = g * B + g ^ 2 * lam + g := by ring
    omega
  have hp : (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * lam + 1 : ℕ) : ℝ)) ^ C₁ ≤ (((g ^ 3 * lam : ℕ) : ℝ) + ((g * (B + g * lam + 1) + g ^ 2 * tOf lam : ℕ) : ℝ)) ^ (3 * C₁) := by
    have h1 : (g ^ 3 * lam + (g * B + g ^ 2 * lam + 1)) ^ C₁ ≤ (g ^ 3 * lam + (g * (B + g * lam + 1) + g ^ 2 * tOf lam)) ^ (3 * C₁) :=
      (Nat.pow_le_pow_left hb C₁).trans (Nat.pow_le_pow_right (by omega) (by omega))
    exact_mod_cast h1
  have ht : ((a * (B + lam) ^ a : ℕ) : ℝ) ≤ ((a * (B + g * lam + 1 + lam) ^ a * 1 : ℕ) : ℝ) := by
    have h1 : a * (B + lam) ^ a ≤ a * (B + g * lam + 1 + lam) ^ a * 1 := by
      rw [Nat.mul_one]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) a)
    exact_mod_cast h1
  have hq : ((B + g * lam + 1 : ℕ) : ℝ) + lam ≤ ((g + 2 : ℕ) : ℝ) * ((B : ℝ) + lam) := by
    have h1 : B + g * lam + 1 + lam ≤ (g + 2) * (B + lam) := by
      have e1 : (g + 2) * (B + lam) = g * B + g * lam + 2 * B + 2 * lam := by ring
      omega
    exact_mod_cast h1
  have hY1 : (1 : ℝ) ≤ (B : ℝ) + lam := by
    have h5 : (1 : ℝ) ≤ lam := by exact_mod_cast hl
    have h6 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
    linarith
  have hq2 : (((B + g * lam + 1 : ℕ) : ℝ) + lam) ^ A1 ≤ ((g + 2 : ℕ) : ℝ) ^ A1 * ((B : ℝ) + lam) ^ A' := by
    calc (((B + g * lam + 1 : ℕ) : ℝ) + lam) ^ A1 ≤ (((g + 2 : ℕ) : ℝ) * ((B : ℝ) + lam)) ^ A1 := pow_le_pow_left₀ (by positivity) hq A1
      _ = ((g + 2 : ℕ) : ℝ) ^ A1 * ((B : ℝ) + lam) ^ A1 := mul_pow _ _ _
      _ ≤ ((g + 2 : ℕ) : ℝ) ^ A1 * ((B : ℝ) + lam) ^ A' := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 (by omega)) (by positivity)
  have hc : (A1 : ℝ) * ((g + 2 : ℕ) : ℝ) ^ A1 ≤ (A' : ℝ) := by
    have h1 : A1 * (g + 2) ^ A1 ≤ A' := by omega
    exact_mod_cast h1
  have hfirst : (((tOf lam + 1) ^ Rn : ℕ) : ℝ) * ((((3 * C₁ : ℕ) : ℝ) + 1) * X1 * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * lam + 1 : ℕ) : ℝ)) ^ C₁ * ((a * (B + lam) ^ a : ℕ) : ℝ)) + 2
      ≤ (((tOf lam + 1) ^ Rn : ℕ) : ℝ) * ((((3 * C₁ : ℕ) : ℝ) + 1) * X1 * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * (B + g * lam + 1) + g ^ 2 * tOf lam : ℕ) : ℝ)) ^ (3 * C₁)
        * ((a * (B + g * lam + 1 + lam) ^ a * 1 : ℕ) : ℝ)) + 2 := by gcongr
  refine hfirst.trans (h.trans ?_)
  calc (A1 : ℝ) * X * (((B + g * lam + 1 : ℕ) : ℝ) + lam) ^ A1 * ((1 : ℕ) : ℝ) = (A1 : ℝ) * X * (((B + g * lam + 1 : ℕ) : ℝ) + lam) ^ A1 := by rw [Nat.cast_one, mul_one]
    _ ≤ (A1 : ℝ) * X * (((g + 2 : ℕ) : ℝ) ^ A1 * ((B : ℝ) + lam) ^ A') := mul_le_mul_of_nonneg_left hq2 (by positivity)
    _ = ((A1 : ℝ) * ((g + 2 : ℕ) : ℝ) ^ A1) * X * ((B : ℝ) + lam) ^ A' := by ring
    _ ≤ (A' : ℝ) * X * ((B : ℝ) + lam) ^ A' := by gcongr
end Printed
