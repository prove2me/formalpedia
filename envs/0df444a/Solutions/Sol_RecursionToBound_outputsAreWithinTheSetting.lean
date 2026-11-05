-- Prove2me | solution 1 for RecursionToBound.outputsAreWithinTheSetting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:59:33.864129+00:00
-- url     : https://prove2.me/submissions/b98926ec-c4b6-44a6-a1c3-609d4dc6511f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Setting
import Definitions.Def_VariableBound_Params_Ineq
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Definitions.Def_RecursionToBound_Numbers
import Theorems.Thm_RecursionToBound_pos_of_le_div
import Theorems.Thm_RecursionToBound_eps_between
import Theorems.Thm_RecursionToBound_occBoundIsThePrinted
import Theorems.Thm_RecursionToBound_pow_eq_two_rpow
import Theorems.Thm_RecursionToBound_lg_eight_div
import Theorems.Thm_RecursionToBound_lg_div_le
import Theorems.Thm_RecursionToBound_lg_le_of_le_pow
import Theorems.Thm_RecursionToBound_lin_lg_le
import Theorems.Thm_RecursionToBound_LD_le_lg
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_VariablesA_settingN0
import Theorems.Thm_VariableBound_paramIneq


set_option autoImplicit false
section
section
open RecursionToBound
open Finset ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution : OutputsAreWithinTheSetting := by
  intro C₀ hC
  obtain ⟨n₀, hn₀⟩ := VariableBound.VariablesA.settingN0 VariableBound.paramIneq C₀ hC
  obtain ⟨N, hN⟩ := exists_nat_ge ((2 : ℝ) ^ ((2 : ℝ) ^ (40 : ℕ)))
  refine ⟨max n₀ N, fun k n Δ r e hn hk hk4 he he1 hr1 hr2 hΔ2 hΔ => ?_⟩
  have hnN : (2 : ℝ) ^ ((2 : ℝ) ^ (40 : ℕ)) ≤ n := hN.trans (by exact_mod_cast (le_max_right _ _).trans hn)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnN
  have hn1 : 1 ≤ n := by exact_mod_cast hn0
  have hL : (2 : ℝ) ^ (40 : ℕ) ≤ lg n := (Real.le_logb_iff_rpow_le one_lt_two hn0).2 hnN
  have hL0 : 0 < lg n := lt_of_lt_of_le (by positivity) hL
  have hLL : 40 ≤ lg (lg n) := by
    refine (Real.le_logb_iff_rpow_le one_lt_two hL0).2 ?_
    rw [show (40 : ℝ) = ((40 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact hL
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) he
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hC' : (1 : ℝ) ≤ C₀ := by exact_mod_cast hC
  obtain ⟨hr1p, hr2p⟩ := pos_of_le_div he0 hr1
  obtain ⟨hε1, -, -⟩ := eps_between he1 hr1 hr2
  -- log Δ ≤ 3k·log(8k/e) + 2
  have c1 : lg Δ ≤ 3 * k * lg (8 * k / e) + 2 := by
    have hae : 8 * (k : ℝ) / ((epsOf r : ℚ) : ℝ) ≤ 8 * k / e := div_le_div_of_nonneg_left (by positivity) he0 hε1
    have ha1 : 1 ≤ 8 * (k : ℝ) / e := by rw [le_div_iff₀ he0]; linarith
    have h1 : (Δ : ℝ) ≤ 2 * (8 * (k : ℝ) / e) ^ (3 * k) + 2 := by
      have h2 : (Δ : ℝ) ≤ occBound k r := by exact_mod_cast hΔ
      have h3 := occBoundIsThePrinted k r hk hr1p hr2p
      have h4 : (8 * (k : ℝ) / ((epsOf r : ℚ) : ℝ)) ^ (3 * k) ≤ (8 * (k : ℝ) / e) ^ (3 * k) :=
        pow_le_pow_left₀ (div_nonneg (by positivity) (he0.le.trans hε1)) hae _
      linarith
    have h5 := lg_le_of_le_pow (by omega) ha1 h1
    push_cast at h5
    exact h5
  -- the middle step
  have c3a : 3 * k * lg (8 * k / e) + 2 ≤ 3 * k * (3 + (C₀ + 1 / 4) * lg (lg n)) + 2 := by
    have h1 := lg_div_le (by omega) hk4 he
    rw [lg_eight_div (by linarith) he0]
    have h2 : 3 * (k : ℝ) * (3 + lg (k / e)) ≤ 3 * k * (3 + (C₀ + 1 / 4) * lg (lg n)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have c3b : 3 * (k : ℝ) * (3 + (C₀ + 1 / 4) * lg (lg n)) + 2 ≤ 4 * k * C₀ * lg (lg n) := by
    have h1 : 0 ≤ (k : ℝ) * lg (lg n) * ((C₀ : ℝ) - 1) := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have h2 : 0 ≤ (k : ℝ) * (lg (lg n) - 40) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  -- Δ ≤ (log n)^(4kC₀)
  have c2 : (Δ : ℝ) ≤ lg n ^ (4 * k * C₀) := by
    have h1 : lg Δ ≤ ((4 * k * C₀ : ℕ) : ℝ) * lg (lg n) := by
      push_cast
      linarith
    rw [pow_eq_two_rpow hL0]
    exact (Real.logb_le_iff_le_rpow one_lt_two (by exact_mod_cast (by omega : 0 < Δ))).1 h1
  -- Δ ≤ n
  have c4 : Δ ≤ n := by
    have h1 := (hn₀ n k Δ ((le_max_left _ _).trans hn) hk4 hΔ2 c2).2.2.1
    have h2 : (n : ℝ) ^ (1 / (40 * C₀ : ℝ)) ≤ (n : ℝ) ^ (1 : ℝ) := by
      refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) ?_
      rw [div_le_one (by positivity)]
      linarith
    rw [Real.rpow_one] at h2
    exact_mod_cast h1.trans h2
  refine ⟨c1, c2, ⟨c3a, c3b⟩, by omega, ?_⟩
  have h1 := LD_le_lg hn1 c4
  have h2 := lin_lg_le hn1 (le_trans (by norm_num) hL)
  have h3 : ((29 * LD Δ + 19 : ℕ) : ℝ) ≤ n := by
    push_cast
    linarith
  exact_mod_cast h3
end RecursionToBound
