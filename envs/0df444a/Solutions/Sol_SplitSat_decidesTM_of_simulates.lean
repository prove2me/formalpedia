-- Prove2me | solution 1 for SplitSat.decidesTM_of_simulates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:34:13.83858+00:00
-- url     : https://prove2.me/submissions/6c072738-1e68-4bee-8eb4-3af2e17f4cba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_SplitSat_Simulate
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_exists_pow_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Paper CountKSat Eight.ViaGrouping
namespace SplitSat
theorem _root_.solution {k : ℕ} {δ : ℝ} (hδ : 0 < δ) {Ms : StepMachine (List Bool) Bool} {M : Turing.TM2ComputableAux Bool Bool} {q c : ℕ}
    (hs : Simulates M Ms q) (h : Decides Ms k (δ / 2) c) : ∃ C : ℕ, c ≤ C ∧ SatK.DecidesTM k M fun n => ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨a, ha⟩ : ∃ a, a = k * 2 ^ k + 1 := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = (c + 1) ^ q * a ^ ((c + 1) * q) := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ := exists_pow_le ((k + 1) * ((c + 1) * q)) hδ2
  refine ⟨q * (c + 1) * (G * C₁) + c, Nat.le_add_left _ _, fun n φ h3 => ?_⟩
  obtain ⟨T, b, hr, hb, hT⟩ := h n φ h3
  obtain ⟨ev⟩ := hs _ b T _ hr
  obtain ⟨X, hX⟩ : ∃ X, X = (SatK.enc k φ).length + 1 := ⟨_, rfl⟩
  have hXa : X ≤ a * (n + 2) ^ (k + 1) := by rw [hX, ha]; exact DecodeK.length_enc_succ_le h3
  have hX1 : 1 ≤ X := by omega
  have hbase : (SatK.enc k φ).length + c * ((SatK.enc k φ).length + 1) ^ c + 1 ≤ (c + 1) * X ^ (c + 1) := by
    rw [← hX]
    have e1 : X ≤ X ^ (c + 1) := Nat.le_self_pow (by omega) _
    have e2 : X ^ c ≤ X ^ (c + 1) := Nat.pow_le_pow_right hX1 (by omega)
    have e3 : c * X ^ c ≤ c * X ^ (c + 1) := Nat.mul_le_mul_left _ e2
    have e4 : (c + 1) * X ^ (c + 1) = c * X ^ (c + 1) + X ^ (c + 1) := by ring
    omega
  obtain ⟨Y, hY⟩ : ∃ Y, Y = ((SatK.enc k φ).length + c * ((SatK.enc k φ).length + 1) ^ c + 1) ^ q := ⟨_, rfl⟩
  have hpow : Y ≤ G * (n + 2) ^ ((k + 1) * ((c + 1) * q)) := by
    rw [hY, hG]
    calc ((SatK.enc k φ).length + c * ((SatK.enc k φ).length + 1) ^ c + 1) ^ q ≤ ((c + 1) * X ^ (c + 1)) ^ q := Nat.pow_le_pow_left hbase q
      _ = (c + 1) ^ q * X ^ ((c + 1) * q) := by rw [mul_pow, ← pow_mul]
      _ ≤ (c + 1) ^ q * (a * (n + 2) ^ (k + 1)) ^ ((c + 1) * q) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hXa _)
      _ = (c + 1) ^ q * a ^ ((c + 1) * q) * (n + 2) ^ ((k + 1) * ((c + 1) * q)) := by rw [mul_pow, ← pow_mul, mul_assoc]
  rw [← hY] at ev
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 2 * n) := ⟨_, rfl⟩
  have hCn := hC₁ n
  rw [← hE] at hCn hT
  have hE1 : (1 : ℝ) ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  have hle : q * (T + 1) * Y ≤ ⌊((q * (c + 1) * (G * C₁) + c : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : ((T : ℝ) + 1) ≤ ((c : ℝ) + 1) * E := by nlinarith
    have h2 : (Y : ℝ) ≤ (G : ℝ) * (C₁ * E) := by
      have h5 : (Y : ℝ) ≤ (G : ℝ) * ((n : ℝ) + 2) ^ ((k + 1) * ((c + 1) * q)) := by exact_mod_cast hpow
      exact h5.trans (mul_le_mul_of_nonneg_left hCn (Nat.cast_nonneg _))
    have h7 : (2 : ℝ) ^ (δ * n) = E * E := by
      rw [hE, ← Real.rpow_add two_pos]; congr 1; ring
    have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
    have hEE : (0 : ℝ) ≤ E * E := by positivity
    push_cast
    rw [h7]
    calc (q : ℝ) * ((T : ℝ) + 1) * (Y : ℝ) ≤ (q : ℝ) * (((c : ℝ) + 1) * E) * ((G : ℝ) * (C₁ * E)) := by gcongr
      _ = ((q : ℝ) * ((c : ℝ) + 1) * ((G : ℝ) * C₁)) * (E * E) := by ring
      _ ≤ ((q : ℝ) * ((c : ℝ) + 1) * ((G : ℝ) * C₁) + c) * (E * E) := mul_le_mul_of_nonneg_right (by linarith) hEE
  exact ⟨b, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩⟩
end SplitSat
