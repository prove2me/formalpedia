-- Prove2me | solution 1 for Printed.level_size_printed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:35:04.353078+00:00
-- url     : https://prove2.me/submissions/cef66f47-ebde-4015-a9e2-bfd10255d226

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelNetworks
import Definitions.Def_Eight_ViaGrouping_Level
import Mathlib.Tactic
import Definitions.Def_Printed_LevelCost
import Theorems.Thm_Eight_Level_level_size
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Printed_poly_absorb
import Theorems.Thm_SingleBitPieces_Level_level_size


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution (g a C₁ Rn : ℕ) : ∃ A2 : ℕ, ∀ sc B lam M : ℕ, 1 ≤ lam → 1 ≤ g → M ≤ 2 * Rn * lam → sc ≤ 2 * (B + lam) + 2 →
    4 * sc + 3 * M + (g * (g ^ 3 * lam + (g * B + g ^ 2 * lam + 1)) + g * g * (g * B + g ^ 2 * lam + 1)) + B + size (g * g) + g * g * (2 * lam + 2) + 30
      + a * (sc + B + lam) ^ a + C₁ * (g ^ 3 * lam + (g * B + g ^ 2 * lam + 1)) ^ C₁ ≤ A2 * (B + lam) ^ A2 := by
  obtain ⟨A, hA⟩ := level_size g a C₁ Rn
  obtain ⟨A2, hA2⟩ := poly_absorb A (2 * Rn + size (g * g) + 4 * (g * g) + 13)
  refine ⟨A2, fun sc B lam M hl hg hM hsc => ?_⟩
  obtain ⟨P, hP⟩ : ∃ P, P = g ^ 3 * lam := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B₁, B₁ = g * B + g ^ 2 * lam + 1 := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = sc + B + lam := ⟨_, rfl⟩
  rw [← hP, ← hB₁, ← hX]
  have h1 := hA sc B lam M P B₁ hl hM hP.le (by
    have e : (g + 2 * g ^ 2) * (B + lam) = g * B + g ^ 2 * lam + (g * lam + 2 * g ^ 2 * B + g ^ 2 * lam) := by ring
    have : 1 ≤ g * lam := Nat.mul_pos hg hl
    omega)
  rw [← hX] at h1
  have h2 := hA2 X (B + lam) (by omega) (by omega)
  have h3 : C₁ * (P + B₁) ^ C₁ ≤ C₁ * (sc + (M + 1) + P + B₁) ^ C₁ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have h4 : size (g * g) ≤ size (g * g) * X := Nat.le_mul_of_pos_right _ (by omega)
  have h5 : g * g * (2 * lam + 2) ≤ g * g * (4 * X) := Nat.mul_le_mul_left _ (by omega)
  have h6 : M ≤ 2 * Rn * X := hM.trans (Nat.mul_le_mul_left _ (by omega))
  have e : (2 * Rn + size (g * g) + 4 * (g * g) + 13) * X = 2 * Rn * X + size (g * g) * X + g * g * (4 * X) + 13 * X := by ring
  omega
end Printed
