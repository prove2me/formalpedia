-- Prove2me | solution 1 for RecursionToBound.oneOutputCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:57:46.451741+00:00
-- url     : https://prove2.me/submissions/2597c6d6-b97b-4534-a838-fe458423d393

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_VariableBound_Top_ArithNat
import Definitions.Def_UniformInK_Top_ArithMaster
import Definitions.Def_VariableBound_Net_Main
import Definitions.Def_VariableBound_Net_StepCost
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Definitions.Def_RecursionToBound_OneOutput
import Theorems.Thm_RecursionToBound_needAt_le
import Theorems.Thm_RecursionToBound_add_three_le_two_pow
import Theorems.Thm_RecursionToBound_six_test
import Theorems.Thm_RecursionToBound_clog_facts
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_VariableBound_VariablesA_one_le_C__74197dd70aad
import Theorems.Thm_UniformInK_stMasterU
import Theorems.Thm_UniformInK_stSixU
import Theorems.Thm_VariableBound_Paper_one_le_lg
import Theorems.Thm_VariableBound_VariablesA_K_le_n
import Theorems.Thm_VariableBound_VariablesA_e_pos
import Theorems.Thm_VariableBound_VariablesA_lg_lt_log_succ


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.ParityChecks UniformInK VariableBound.Net MainTheoremForms VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution : OneOutputCost := by
  intro Idx _ S e C₀ Q _
  refine ⟨420 + (VariableBound.ccD 0 C₀ + 140) * A1U C₀, 2 ^ ((520200 * C₀ ^ 4) ^ 2), fun k n l Δ hn hl hk hk4 hΔ2 hΔ => ?_⟩
  have hC := VariableBound.VariablesA.one_le_C₀ Q
  have hK := Q.K_two l
  have hlt : n < S.K (Q.idx l) ^ (17 * C₀) := lt_of_lt_of_le hl.2 (by rw [Nat.mul_comm, pow_mul]; exact Nat.pow_le_pow_left (Q.K_le l) 17)
  have hKn := VariableBound.VariablesA.K_le_n Q hl
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Nat.log 2 n := ⟨_, rfl⟩
  have hℓB : (520200 * C₀ ^ 4) ^ 2 ≤ ℓ := hℓ ▸ Nat.le_log_of_pow_le (by norm_num) hn
  have hℓ1 : 1 ≤ ℓ := le_trans (Nat.one_le_pow _ _ (Nat.mul_pos (by norm_num) (pow_pos hC 4))) hℓB
  have hk4ℓ : k ^ 4 ≤ ℓ := by
    have h1 : (((k ^ 4 : ℕ) : ℕ) : ℝ) ≤ lg n := by push_cast; exact hk4
    have h2 := (Real.le_logb_iff_rpow_le one_lt_two hn0).1 h1
    rw [Real.rpow_natCast] at h2
    exact hℓ ▸ Nat.le_log_of_pow_le (by norm_num) (by exact_mod_cast h2)
  have hlgℓ : lg n ≤ ((ℓ + 1 : ℕ) : ℝ) := by
    have := VariableBound.VariablesA.lg_lt_log_succ hn1
    rw [hℓ]
    push_cast
    exact this.le
  have hL0 : 0 ≤ lg n := le_trans (by positivity) hk4
  obtain ⟨hc1, hc2, hc3⟩ := clog_facts hΔ2
  obtain ⟨β₁, hβ₁⟩ : ∃ β₁, β₁ = Nat.clog 2 Δ := ⟨_, rfl⟩
  rw [← hβ₁] at hc1 hc2 hc3
  have hΔℓ : Δ ≤ (ℓ + 1) ^ (4 * k * C₀) := by
    have : (Δ : ℝ) ≤ (((ℓ + 1) ^ (4 * k * C₀) : ℕ) : ℝ) := by
      rw [Nat.cast_pow]
      exact hΔ.trans (pow_le_pow_left₀ hL0 hlgℓ _)
    exact_mod_cast this
  have hD1 : 2 ^ β₁ ≤ (ℓ + 1) ^ (4 * k * C₀ + 1) := by
    rw [pow_succ, Nat.mul_comm]
    exact hc1.trans (Nat.mul_le_mul (by omega) hΔℓ)
  have hD2 : 2 ^ k ≤ (ℓ + 1) ^ (4 * k * C₀ + 1) :=
    (Nat.pow_le_pow_left (by omega) k).trans (Nat.pow_le_pow_right (by omega) (by nlinarith [Nat.mul_pos (by omega : 0 < k) hC]))
  have hDle : 2 ^ max β₁ k ≤ (Nat.log 2 n + 1) ^ (4 * k * C₀ + 1) := by
    rw [← hℓ]
    rcases le_total β₁ k with h | h
    · rw [max_eq_right h]; exact hD2
    · rw [max_eq_left h]; exact hD1
  have h6 : (2 ^ max β₁ k) ^ 6 ≤ S.K (Q.idx l) :=
    stSixU _ (4 * k * C₀ + 1) _ n C₀ (by omega) hn1 hlt hDle (hℓ ▸ six_test hC (by omega) hℓB hk4ℓ)
  have hbD : max β₁ k + 3 ≤ 2 ^ max β₁ k := add_three_le_two_pow (hk.trans (le_max_right _ _))
  have hD : 2 ^ max β₁ k ≤ n + 1 := ((Nat.le_self_pow (by norm_num) _).trans h6).trans (hKn.trans (Nat.le_succ n))
  have hM := stMasterU (max β₁ k) _ C₀ (e l) hbD hK (Q.e_ge l) h6
  have main := needAt_le S (Q.idx l) (k := k) hK hl.1 hlt hc2 (hβ₁ ▸ Nat.le_pow_clog (by norm_num) Δ) (le_max_left _ _) (le_max_right _ _) hbD hD
    (VariableBound.VariablesA.e_pos Q l) (Q.e_le l) hM (Q.rate l)
  refine main.trans ?_
  have he0 := (VariableBound.VariablesA.e_pos Q l).le
  have hw := one_le_lg hΔ2
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hy0 : 0 ≤ (n : ℝ) * e l := mul_nonneg hn0.le he0
  have s0 : VariableBound.ccD k C₀ * A1U C₀ ≤ (VariableBound.ccD 0 C₀ + 140) * A1U C₀ * k := by
    have : VariableBound.ccD k C₀ ≤ (VariableBound.ccD 0 C₀ + 140) * k := by
      have e1 : VariableBound.ccD k C₀ = VariableBound.ccD 0 C₀ + 140 * k := by unfold VariableBound.ccD; ring
      rw [e1]
      nlinarith [Nat.zero_le (VariableBound.ccD 0 C₀)]
    calc VariableBound.ccD k C₀ * A1U C₀ ≤ (VariableBound.ccD 0 C₀ + 140) * k * A1U C₀ := Nat.mul_le_mul_right _ this
      _ = _ := by ring
  have s1 : ((VariableBound.ccD k C₀ * A1U C₀ : ℕ) : ℝ) ≤ (((VariableBound.ccD 0 C₀ + 140) * A1U C₀ : ℕ) : ℝ) * k := by exact_mod_cast s0
  have s2 : (n : ℝ) * e l ≤ (n : ℝ) * e l * lg Δ := le_mul_of_one_le_right hy0 hw
  have t2 : ((VariableBound.ccD k C₀ * A1U C₀ : ℕ) : ℝ) * ((n : ℝ) * e l) ≤ (((VariableBound.ccD 0 C₀ + 140) * A1U C₀ : ℕ) : ℝ) * k * ((n : ℝ) * e l * lg Δ) :=
    mul_le_mul s1 s2 hy0 (by positivity)
  have t1 : e l * (140 * (k : ℝ) * n * ((β₁ + 1 : ℕ) : ℝ)) ≤ e l * (140 * (k : ℝ) * n * (3 * lg Δ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc3 (by positivity)) he0
  have e1 : ((420 + (VariableBound.ccD 0 C₀ + 140) * A1U C₀ : ℕ) : ℝ) * e l * k * n * lg Δ =
      e l * (140 * (k : ℝ) * n * (3 * lg Δ)) + (((VariableBound.ccD 0 C₀ + 140) * A1U C₀ : ℕ) : ℝ) * k * ((n : ℝ) * e l * lg Δ) := by
    rw [Nat.cast_add]
    push_cast
    ring
  rw [e1]
  linarith
end RecursionToBound
