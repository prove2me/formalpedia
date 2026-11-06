-- Prove2me | solution 1 for Printed.cost_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:33:01.251744+00:00
-- url     : https://prove2.me/submissions/5eee856b-1278-4724-b8a6-ddaa3376844a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Count
import Theorems.Thm_Printed_length_lt_size
import Theorems.Thm_Eight_ViaGrouping_mul_satPf_le
import Theorems.Thm_Eight_ViaGrouping_satPf_le
import Theorems.Thm_Eight_ViaGrouping_size_bound
import Theorems.Thm_Eight_network_total_lt
import Theorems.Thm_Eight_network_total_nil
import Theorems.Thm_Eight_network_value_eq
import Theorems.Thm_Eight_remaining_factor
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_mu_le
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Prog_length_lt_size
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_Eight_network_exponent_lt__a4989babe798
import Theorems.Thm_P2M_SingleBitPieces_network_exponent_le__a6ed8dab0b4b
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
import Theorems.Thm_SingleBitPieces_exponent_eq
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines
namespace Printed
theorem _root_.solution {g K : ℕ} {δ' : ℝ} {Mc : Stepped Fml ℤ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hg : 0 < g) (hK : 72 / δ' ≤ K)
    (h : ∃ C₁ : ℕ, ∀ Φ : Fml, ∃ T : ℕ,
      Mc.Runs Φ T (size Φ + 2 * g + 6 * (mu g Φ * 3) + 10 + C₁ * (size Φ + satPf g 3 Φ + 1) ^ C₁) (wordNet g 3 Φ).value ∧
      (T : ℝ) ≤ C₁ * (2 : ℝ) ^ (δ' / 12 * ((wordNet g 3 Φ).U : ℝ) + (δ' / 12 + 2) * ((g : ℝ) * (satPf g 3 Φ : ℝ)) / K) * ((satPf g 3 Φ : ℝ) + 1) ^ C₁) :
    ∃ A : ℕ, ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) →
      ∃ T : ℕ, Mc.Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length) := by
  obtain ⟨C₁, hC₁⟩ := h
  -- «The remaining factor … is polynomial in m, hence O(2^{δ'm/4}).»
  obtain ⟨A₁, hA₁⟩ := Eight.remaining_factor C₁ g hδ'
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ, A = (6 * 3 + 2 * g + 11) + C₁ * (2 * 3 + 3) ^ C₁ + C₁ + 1 + 2 ^ C₁ * A₁ := ⟨_, rfl⟩
  refine ⟨A, fun Φ hΦ => ?_⟩
  obtain ⟨T, hrun, hT⟩ := hC₁ Φ
  obtain ⟨m, hm⟩ : ∃ m, m = Φ.length := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = mu g Φ := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = size Φ := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = satPf g 3 Φ := ⟨_, rfl⟩
  have hms : m + 1 ≤ s := by rw [hm, hs]; exact length_lt_size Φ
  have hμm : μ ≤ m := by rw [hm, hμ]; exact mu_le hg Φ
  have hP1 : P ≤ 2 * (μ * 3) + 1 := by rw [hP, hμ]; exact Eight.ViaGrouping.satPf_le g 3 Φ
  -- «Hence Z is the number of assignments of the variables occurring in Φ that satisfy Φ.»
  have hZ : (wordNet g 3 Φ).value = numSat Φ := Eight.network_value_eq hg Φ hΦ
  rw [hZ, ← hP, ← hμ, ← hs] at hrun
  rw [← hP] at hT
  rw [← hm, ← hs]
  refine ⟨T, hrun.mono le_rfl (Eight.ViaGrouping.size_bound (by omega) hP1 (by omega)), ?_⟩
  -- «gP = 6g⌈m/g⌉ ≤ 6(m + g)»
  have hgP : g * P ≤ 6 * (m + g) := by rw [hP, hm]; exact Eight.ViaGrouping.mul_satPf_le (by norm_num) g Φ
  -- «the exponent in Lemma 1 is … ≤ ¾δ'm + δ'g»
  have hexp : δ' / 12 * (((wordNet g 3 Φ).U : ℕ) : ℝ) + (δ' / 12 + 2) * ((g : ℝ) * P) / K ≤ 3 / 4 * δ' * m + δ' * g := by
    rw [SingleBitPieces.exponent_eq]
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · -- m = 0
      have hnil : Φ = [] := List.eq_nil_of_length_eq_zero (hm ▸ h0)
      have hU0 : (wordNet g 3 Φ).U ≤ 6 * m := by rw [hnil]; exact (Eight.network_total_nil hg).le.trans (Nat.zero_le _)
      exact SingleBitPieces.network_exponent_le' hδ' h1 hK hU0 hgP
    · -- m ≥ 1: «U ≤ 2(3m − 1) < 6m»
      have hU : (wordNet g 3 Φ).U < 6 * m := hm ▸ Eight.network_total_lt hg hΦ (hm ▸ h0)
      exact (Eight.network_exponent_lt' hδ' h1 hK hU hgP).le
  have hE : (2 : ℝ) ^ (δ' / 12 * (((wordNet g 3 Φ).U : ℕ) : ℝ) + (δ' / 12 + 2) * ((g : ℝ) * P) / K) ≤ (2 : ℝ) ^ (3 / 4 * δ' * m) * (2 : ℝ) ^ (δ' * g) := by
    rw [← Real.rpow_add two_pos]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two hexp
  -- P + B = 6m̄ + 1 for m ≥ 1; for m = 0 it is 2
  have hPB : (P : ℝ) + 1 ≤ 2 * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) := by
    have : P + 1 ≤ 2 * (6 * ((m + g - 1) / g) + 1) := by
      have e : (m + g - 1) / g = μ := by rw [hm, hμ]; rfl
      rw [e]; omega
    exact_mod_cast this
  have hsplit : (2 : ℝ) ^ (3 / 4 * δ' * m) * (2 : ℝ) ^ (δ' * m / 4) = (2 : ℝ) ^ (δ' * m) := by
    rw [← Real.rpow_add two_pos]
    congr 1
    ring
  calc (T : ℝ) ≤ C₁ * (2 : ℝ) ^ (δ' / 12 * (((wordNet g 3 Φ).U : ℕ) : ℝ) + (δ' / 12 + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + 1) ^ C₁ := hT
    _ ≤ C₁ * ((2 : ℝ) ^ (3 / 4 * δ' * m) * (2 : ℝ) ^ (δ' * g)) * (2 * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ)) ^ C₁ := by gcongr
    _ = 2 ^ C₁ * (2 : ℝ) ^ (3 / 4 * δ' * m) * ((C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * (((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ)) ^ C₁) := by rw [mul_pow]; ring
    _ ≤ 2 ^ C₁ * (2 : ℝ) ^ (3 / 4 * δ' * m) * (A₁ * (2 : ℝ) ^ (δ' * m / 4)) := mul_le_mul_of_nonneg_left (hA₁ m) (by positivity)
    _ = ((2 ^ C₁ * A₁ : ℕ) : ℝ) * (2 : ℝ) ^ (δ' * m) := by rw [← hsplit]; push_cast; ring
    _ ≤ A * (2 : ℝ) ^ (δ' * m) := by
        gcongr
        omega
end Printed
