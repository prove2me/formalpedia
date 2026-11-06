-- Prove2me | solution 1 for Sat3Graph.outputs_of_simulates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:36:51.784899+00:00
-- url     : https://prove2.me/submissions/82ffe59b-20fc-4d14-bab2-f7104d07dd25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_GraphProblems_Read
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Host
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_exists_pow_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog GraphProblems Paper SplitSat
namespace Sat3Graph
theorem _root_.solution {M : Turing.TM2ComputableAux Bool Bool} {Ms : StepMachine (List Bool) Bool} {q : ℕ} (hs : Simulates M Ms q)
    {δ : ℝ} (hδ : 0 < δ) (c : ℕ) : ∃ C : ℕ, ∀ (n : ℕ) (x : List Bool) (b : Bool) (T : ℕ), x.length ≤ 2 * (n + 2) ^ 2 →
      Ms.Runs x T (c * (n + 2) ^ c) b → (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / 2 * n) → Outputs M x [b] ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨G, hG⟩ : ∃ G, G = (c + 3) ^ q := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ := exists_pow_le ((c + 2) * q) hδ2
  refine ⟨q * (c + 1) * (G * C₁), fun n x b T hx hr hT => ?_⟩
  obtain ⟨ev⟩ := hs x b T _ hr
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  rw [← hX] at hx ev
  have hX1 : 1 ≤ X := by omega
  have hbase : x.length + c * X ^ c + 1 ≤ (c + 3) * X ^ (c + 2) := by
    have e0 : 1 ≤ X ^ (c + 2) := Nat.one_le_pow _ _ hX1
    have e1 : X ^ 2 ≤ X ^ (c + 2) := Nat.pow_le_pow_right hX1 (by omega)
    have e2 : X ^ c ≤ X ^ (c + 2) := Nat.pow_le_pow_right hX1 (by omega)
    have e3 : c * X ^ c ≤ c * X ^ (c + 2) := Nat.mul_le_mul_left _ e2
    have e4 : (c + 3) * X ^ (c + 2) = c * X ^ (c + 2) + 3 * X ^ (c + 2) := by ring
    omega
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (x.length + c * X ^ c + 1) ^ q := ⟨_, rfl⟩
  have hpow : Y ≤ G * (n + 2) ^ ((c + 2) * q) := by
    rw [hY, hG, ← hX]
    calc (x.length + c * X ^ c + 1) ^ q ≤ ((c + 3) * X ^ (c + 2)) ^ q := Nat.pow_le_pow_left hbase q
      _ = (c + 3) ^ q * X ^ ((c + 2) * q) := by rw [mul_pow, ← pow_mul]
  rw [← hY] at ev
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 2 * n) := ⟨_, rfl⟩
  have hCn := hC₁ n
  rw [← hE] at hCn hT
  have hE1 : (1 : ℝ) ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  have hle : q * (T + 1) * Y ≤ ⌊((q * (c + 1) * (G * C₁) : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : ((T : ℝ) + 1) ≤ ((c : ℝ) + 1) * E := by nlinarith
    have h2 : (Y : ℝ) ≤ (G : ℝ) * (C₁ * E) := by
      have h5 : (Y : ℝ) ≤ (G : ℝ) * ((n : ℝ) + 2) ^ ((c + 2) * q) := by exact_mod_cast hpow
      exact h5.trans (mul_le_mul_of_nonneg_left hCn (Nat.cast_nonneg _))
    have h7 : (2 : ℝ) ^ (δ * n) = E * E := by
      rw [hE, ← Real.rpow_add two_pos]
      congr 1
      ring
    push_cast
    rw [h7]
    calc (q : ℝ) * ((T : ℝ) + 1) * (Y : ℝ) ≤ (q : ℝ) * (((c : ℝ) + 1) * E) * ((G : ℝ) * (C₁ * E)) := by gcongr
      _ = ((q : ℝ) * ((c : ℝ) + 1) * ((G : ℝ) * C₁)) * (E * E) := by ring
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩
end Sat3Graph
