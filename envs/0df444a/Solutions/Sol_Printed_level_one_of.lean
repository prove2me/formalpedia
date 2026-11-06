-- Prove2me | solution 1 for Printed.level_one_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:36.012473+00:00
-- url     : https://prove2.me/submissions/12634bad-81d3-4ddb-917d-b3779fac119e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelNetworks
import Definitions.Def_Eight_ViaGrouping_Level
import Mathlib.Tactic
import Definitions.Def_Printed_LevelCost
import Theorems.Thm_Eight_Level_stMin
import Theorems.Thm_Eight_ViaGrouping_U_levelNetP
import Theorems.Thm_Eight_ViaGrouping_value_levelNetP
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Stepped_ite_runs_false
import Theorems.Thm_Groundwork_Stepped_ite_runs_true
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution (hO : StOnProcedures) {K g C₁ a : ℕ} {e : ℝ} {NM : NetMachine} (h0 : 0 ≤ e) (hg1 : 1 ≤ g) (hNM : ComputesNetworks NM C₁ g K e)
    {c : List Unit × List Unit} {lam B S y : ℕ} {O : TableQuery → Option ℤ} {Rm : Inst (Fin (g * g)) (List Bool)} (hcl : c.1.length = lam) (hl : 1 ≤ lam)
    (hnet : ∀ tr, SecNetworks.IsNetwork ((gridProcs g tr).close O) (c, y) (levelNetP g tr lam y Rm) (g ^ 3 * lam) (g * B + g ^ 2 * lam + 1) (a * (B + lam) ^ a) S) :
    ∃ τ : ℕ, (Stepped.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOnSteps g NM ((gridProcs g false).close O)) (networkOnSteps g NM ((gridProcs g true).close O))).Runs (c, y) τ
        (size (c, y) + C₁ * (g ^ 3 * lam + (g * B + g ^ 2 * lam + 1)) ^ C₁ + S + 4 + 1) (Eight.Zι (gridR0 g g lam Rm) (Level.patOf g lam y)) ∧
      (τ : ℝ) + 1 ≤ (((3 * C₁ : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (e * (rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4) + (e + 2) * ((g : ℝ) * ((g ^ 3 * lam : ℕ) : ℝ)) / K)
        * (((g ^ 3 * lam : ℕ) : ℝ) + ((g * B + g ^ 2 * lam + 1 : ℕ) : ℝ)) ^ C₁ * ((a * (B + lam) ^ a : ℕ) : ℝ) := by
  obtain ⟨P, hP⟩ : ∃ P, P = g ^ 3 * lam := ⟨_, rfl⟩
  obtain ⟨B₁, hB₁⟩ : ∃ B₁, B₁ = g * B + g ^ 2 * lam + 1 := ⟨_, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t', t' = a * (B + lam) ^ a := ⟨_, rfl⟩
  obtain ⟨Ub, hUb⟩ : ∃ Ub : ℝ, Ub = rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4 := ⟨_, rfl⟩
  rw [← hP, ← hB₁, ← ht', ← hUb]
  rw [← hP, ← hB₁, ← ht'] at hnet
  have hP1 : 1 ≤ P := by rw [hP]; exact Nat.mul_pos (pow_pos hg1 3) hl
  have ht'1 : 1 ≤ t' := (hnet false).τ_pos
  obtain ⟨Nr, hNr⟩ : ∃ Nr : Net g, Nr = levelNetP g false lam y Rm := ⟨_, rfl⟩
  obtain ⟨Nc, hNc⟩ : ∃ Nc : Net g, Nc = levelNetP g true lam y Rm := ⟨_, rfl⟩
  have hpr : SecNetworks.IsNetwork ((gridProcs g false).close O) (c, y) Nr P B₁ t' S := by rw [hNr]; exact hnet false
  have hpc : SecNetworks.IsNetwork ((gridProcs g true).close O) (c, y) Nc P B₁ t' S := by rw [hNc]; exact hnet true
  have hvr : Nr.value = Eight.Zι (gridR0 g g lam Rm) (Level.patOf g lam y) := by rw [hNr]; exact value_levelNetP hl g false y Rm
  have hvc : Nc.value = Eight.Zι (gridR0 g g lam Rm) (Level.patOf g lam y) := by rw [hNc]; exact value_levelNetP hl g true y Rm
  have hur : Nr.U = totalG eightF g g false 0 lam y := by rw [hNr]; exact U_levelNetP g false lam y Rm
  have huc : Nc.U = totalG eightF g g true 0 lam y := by rw [hNc]; exact U_levelNetP g true lam y Rm
  have hmin := stMin g lam y hl
  have tail : ∀ U τ : ℕ, U ≤ min (totalG eightF g g false 0 lam y) (totalG eightF g g true 0 lam y) →
      (τ : ℝ) ≤ 3 * ((C₁ : ℝ) * (2 : ℝ) ^ (e * ((U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B₁) ^ C₁) * t' →
      (τ : ℝ) + 1 ≤ (((3 * C₁ : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B₁) ^ C₁ * t' := by
    intro U τ hU hτ
    have hU' : (U : ℝ) ≤ Ub := by
      have : (U : ℝ) ≤ ((min (totalG eightF g g false 0 lam y) (totalG eightF g g true 0 lam y) : ℕ) : ℝ) := by exact_mod_cast hU
      rw [hUb]
      linarith
    have hUb0 : 0 ≤ Ub := le_trans (Nat.cast_nonneg U) hU'
    have hX : (1 : ℝ) ≤ (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) :=
      Real.one_le_rpow (by norm_num)
        (add_nonneg (mul_nonneg h0 hUb0) (div_nonneg (mul_nonneg (by linarith) (by positivity)) (Nat.cast_nonneg _)))
    have hY : (1 : ℝ) ≤ ((P : ℝ) + B₁) ^ C₁ := by
      refine one_le_pow₀ ?_
      have h5 : (1 : ℝ) ≤ P := by exact_mod_cast hP1
      have h6 : (0 : ℝ) ≤ (B₁ : ℝ) := Nat.cast_nonneg _
      linarith
    have htr : (1 : ℝ) ≤ t' := by exact_mod_cast ht'1
    have h3 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hX hY) htr
    have hexp : e * ((U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K ≤ e * Ub + (e + 2) * ((g : ℝ) * P) / K := by
      have e1 : e * ((U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K = e * U + (e + 2) * ((g : ℝ) * P) / K := by ring
      have e2 := mul_le_mul_of_nonneg_left hU' h0
      rw [e1]
      linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    have e3 : ((3 * C₁ : ℕ) : ℝ) = 3 * (C₁ : ℝ) := by push_cast; ring
    have h4 : (τ : ℝ) ≤ ((3 * C₁ : ℕ) : ℝ) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B₁) ^ C₁ * t' := by
      refine hτ.trans ?_
      rw [e3]
      calc 3 * ((C₁ : ℝ) * (2 : ℝ) ^ (e * ((U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B₁) ^ C₁) * t'
          ≤ 3 * ((C₁ : ℝ) * (2 : ℝ) ^ (e * Ub + (e + 2) * ((g : ℝ) * P) / K) * ((P : ℝ) + B₁) ^ C₁) * t' := by gcongr
        _ = _ := by ring
    calc _ ≤ _ := add_le_add h4 h3
      _ = _ := by ring
  by_cases hu : totalG eightF g g false 0 lam y ≤ totalG eightF g g true 0 lam y
  · obtain ⟨τ, hτ1, hτ2⟩ := hO NM C₁ g K e hNM _ ((gridProcs g false).close O) (c, y) Nr P B₁ t' S hpr
    rw [hvr] at hτ1
    have hdec : useRowP g (fun c : List Unit × List Unit => c.1.length) (c, y) = true := by
      show decide (totalG eightF g g false 0 c.1.length y ≤ totalG eightF g g true 0 c.1.length y) = true
      rw [hcl]
      exact decide_eq_true hu
    exact ⟨τ, Stepped.ite_runs_true hdec hτ1, tail _ _ (by rw [min_eq_left hu, hur]) hτ2⟩
  · obtain ⟨τ, hτ1, hτ2⟩ := hO NM C₁ g K e hNM _ ((gridProcs g true).close O) (c, y) Nc P B₁ t' S hpc
    rw [hvc] at hτ1
    have hdec : useRowP g (fun c : List Unit × List Unit => c.1.length) (c, y) = false := by
      show decide (totalG eightF g g false 0 c.1.length y ≤ totalG eightF g g true 0 c.1.length y) = false
      rw [hcl]
      exact decide_eq_false hu
    exact ⟨τ, Stepped.ite_runs_false hdec hτ1, tail _ _ (by rw [min_eq_right (not_le.1 hu).le, huc]) hτ2⟩
end Printed
