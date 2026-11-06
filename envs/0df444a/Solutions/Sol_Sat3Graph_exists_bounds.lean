-- Prove2me | solution 1 for Sat3Graph.exists_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:35:22.149185+00:00
-- url     : https://prove2.me/submissions/396a1584-94f1-415b-a5a0-71f17b6acf5c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SizeCircuit_General
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Split
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Eight.Width
namespace Sat3Graph
theorem _root_.solution (A c : ℕ) {δ δ₃ : ℝ} (h0 : 0 ≤ δ₃) (hle : δ₃ * (A : ℝ) ≤ δ) : ∃ c' : ℕ, ∀ n N T : ℕ, N ≤ A * (n + 1) →
    (T : ℝ) ≤ c * (2 : ℝ) ^ (δ₃ * N) → c * (N + 2) ^ c ≤ c' * (n + 2) ^ c' ∧ (T : ℝ) ≤ c' * (2 : ℝ) ^ (δ * n) := by
  obtain ⟨c₁, hc₁⟩ := exists_nat_ge ((c : ℝ) * (2 : ℝ) ^ δ)
  obtain ⟨C', hC'⟩ : ∃ C', C' = c₁ + c * (A + 2) ^ c + c := ⟨_, rfl⟩
  have k1 : c₁ ≤ C' := by rw [hC', Nat.add_assoc]; exact Nat.le_add_right _ _
  have k2 : c * (A + 2) ^ c ≤ C' := by rw [hC']; exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  have k3 : c ≤ C' := by rw [hC']; exact Nat.le_add_left _ _
  refine ⟨C', fun n N T hN hT => ⟨?_, ?_⟩⟩
  · obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
    rw [← hX]
    have hX1 : 1 ≤ X := by omega
    have h3 : N + 2 ≤ (A + 2) * X := by
      have e1 : A * (n + 1) ≤ A * X := Nat.mul_le_mul_left _ (by omega)
      have e2 : (A + 2) * X = A * X + 2 * X := by ring
      omega
    calc c * (N + 2) ^ c ≤ c * ((A + 2) * X) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h3 _)
      _ = c * (A + 2) ^ c * X ^ c := by rw [Nat.mul_pow, Nat.mul_assoc]
      _ ≤ C' * X ^ C' := Nat.mul_le_mul k2 (Nat.pow_le_pow_right hX1 k3)
  · have hN' : (N : ℝ) ≤ (A : ℝ) * ((n : ℝ) + 1) := by exact_mod_cast hN
    have h1 : δ₃ * N ≤ δ * n + δ := by
      calc δ₃ * N ≤ δ₃ * ((A : ℝ) * ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left hN' h0
        _ = δ₃ * (A : ℝ) * ((n : ℝ) + 1) := by ring
        _ ≤ δ * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right hle (by positivity)
        _ = δ * n + δ := by ring
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (δ * n) := by positivity
    calc (T : ℝ) ≤ c * (2 : ℝ) ^ (δ₃ * N) := hT
      _ ≤ c * (2 : ℝ) ^ (δ * n + δ) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two h1) (Nat.cast_nonneg c)
      _ = c * (2 : ℝ) ^ δ * (2 : ℝ) ^ (δ * n) := by
        rw [Real.rpow_add two_pos]
        ring
      _ ≤ c₁ * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right hc₁ hp
      _ ≤ C' * (2 : ℝ) ^ (δ * n) := mul_le_mul_of_nonneg_right (Nat.cast_le.2 k1) hp
end Sat3Graph
