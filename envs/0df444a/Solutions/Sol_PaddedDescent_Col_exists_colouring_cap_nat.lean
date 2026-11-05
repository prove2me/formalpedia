-- Prove2me | solution 1 for PaddedDescent.Col.exists_colouring_cap_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:04:19.539811+00:00
-- url     : https://prove2.me/submissions/ae6ea33a-fc23-4ee9-b381-10c6cc70191f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push
import Definitions.Def_PaddedDescent_Col_Colouring
import Theorems.Thm_PaddedDescent_Col_exists_colouring_cap
import Theorems.Thm_PaddedDescent_Col_two_pow_le_exp

set_option autoImplicit false
section
section
open Finset
open PaddedDescent PaddedDescent.Col
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace PaddedDescent.Col
theorem _root_.solution {K g : ℕ} (hK : 1 ≤ K) (c : Fin g → Fin g → ℕ) (M D m : ℕ) (hM0 : 0 < M) (hD : 1 ≤ D)
    (hM : ∀ a b, c a b ≤ M) (h1 : 4 * D ^ 2 * m * K ≤ g) (h2 : (g + 2) * K < 2 ^ m) :
    ∃ χ : Fin g → Fin K, (∀ G, K * #{a | χ a = G} < 2 * g) ∧
      ∀ G G', D * K ^ 2 * ∑ a with χ a = G, ∑ b with χ b = G', c a b ≤ D * (∑ a, ∑ b, c a b) + 3 * g ^ 2 * M := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have key : ((Fintype.card (Fin g) : ℝ) + 2) * Fintype.card (Fin K) *
      Real.exp (-((1 / (D : ℝ)) ^ 2 * ((Fintype.card (Fin g) : ℝ) / Fintype.card (Fin K)) / 4)) < 1 := by
    simp only [Fintype.card_fin]
    have a1 : (m : ℝ) ≤ (1 / (D : ℝ)) ^ 2 * ((g : ℝ) / K) / 4 := by
      have h1r : (4 : ℝ) * D ^ 2 * m * K ≤ g := by exact_mod_cast h1
      have e : (1 / (D : ℝ)) ^ 2 * ((g : ℝ) / K) / 4 = g / (4 * D ^ 2 * K) := by field_simp
      rw [e, le_div_iff₀ (by positivity)]
      linarith
    have a2 : Real.exp (-((1 / (D : ℝ)) ^ 2 * ((g : ℝ) / K) / 4)) ≤ 1 / 2 ^ m := by
      calc Real.exp (-((1 / (D : ℝ)) ^ 2 * ((g : ℝ) / K) / 4)) ≤ Real.exp (-(m : ℝ)) := Real.exp_le_exp.2 (by linarith)
        _ = 1 / Real.exp m := by rw [Real.exp_neg, one_div]
        _ ≤ 1 / 2 ^ m := by
            apply one_div_le_one_div_of_le (by positivity) (two_pow_le_exp m)
    have a3 : ((g : ℝ) + 2) * K < 2 ^ m := by exact_mod_cast h2
    calc ((g : ℝ) + 2) * K * Real.exp (-((1 / (D : ℝ)) ^ 2 * ((g : ℝ) / K) / 4)) ≤ ((g : ℝ) + 2) * K * (1 / 2 ^ m) := by gcongr
      _ = ((g : ℝ) + 2) * K / 2 ^ m := by ring
      _ < 1 := by rw [div_lt_one (by positivity)]; exact a3
  simpa only [Fintype.card_fin] using exists_colouring_cap (ι := Fin g) (κ := Fin K) c M D hM0 hD hM key
end PaddedDescent.Col
