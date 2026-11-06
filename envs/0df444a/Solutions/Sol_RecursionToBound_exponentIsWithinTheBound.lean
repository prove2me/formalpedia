-- Prove2me | solution 1 for RecursionToBound.exponentIsWithinTheBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:10:01.268732+00:00
-- url     : https://prove2.me/submissions/b30e6578-6a7c-4547-8ec8-7b0b5f16589b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_RecursionToBound_OneOutput
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_ClauseBound_Gen_RateAux
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_RecursionToBound_Exponent
import Theorems.Thm_RecursionToBound_walkCost
import Theorems.Thm_RecursionToBound_foldr_max_zero_le
import Theorems.Thm_RecursionToBound_of_mem_deltas
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_VariableBound_VariablesA_one_le_C__74197dd70aad
import Theorems.Thm_RecursionToBound_eps_between
import Theorems.Thm_RecursionToBound_lg_eight_div
import Theorems.Thm_RecursionToBound_oneOutputCost
import Theorems.Thm_RecursionToBound_outputsAreWithinTheSetting
import Theorems.Thm_RecursionToBound_pos_of_le_div
import Theorems.Thm_VariableBound_Net_FitL_lg_mono
import Theorems.Thm_VariableBound_Paper_lg_mono
import Theorems.Thm_VariableBound_Paper_one_le_lg
import Theorems.Thm_VariableBound_VariablesA_e_ge_n
import Theorems.Thm_VariableBound_VariablesA_e_pos
import Theorems.Thm_VariableBound_VariablesA_lg_div_facts
import Theorems.Thm_VariableBound_VariablesA_stepSparsifyLarge


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen.Rate ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution : ExponentIsWithinTheBound := by
  intro Idx _ S e C₀ Q hS num hnum
  obtain ⟨A₁, n₁a, hA⟩ := oneOutputCost Idx S e C₀ Q hS
  obtain ⟨c, hc⟩ := walkCost
  obtain ⟨n₁b, hb⟩ := outputsAreWithinTheSetting C₀ (VariableBound.VariablesA.one_le_C₀ Q)
  obtain ⟨n₁c, hcL⟩ := VariableBound.VariablesA.stepSparsifyLarge C₀
  refine ⟨14 * A₁ + 2 + 5 * c, max (max n₁a n₁b) (max n₁c 2), fun k n l hn hl hk hk4 => ?_⟩
  have hna : n₁a ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hnb : n₁b ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans hn
  have hnc : n₁c ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn2 : 2 ≤ n := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  have he0 := VariableBound.VariablesA.e_pos Q l
  have he1 := Q.e_le l
  have hen := VariableBound.VariablesA.e_ge_n Q hl
  obtain ⟨hr1, hr2⟩ := hnum.2 l
  generalize num (List.replicate l (), List.replicate (S.K (Q.idx l)) ()) = r at hr1 hr2 ⊢
  obtain ⟨hr1p, hr2p⟩ := pos_of_le_div he0 hr1
  obtain ⟨hε1, hε2, -⟩ := eps_between he1 hr1 hr2
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨w1, w2⟩ := VariableBound.VariablesA.lg_div_facts hk he0 he1
  have hw : 1 ≤ lg (k / e l) := w1.trans w2
  have hklg := hcL k n (e l) hnc hk4 hen
  have hL := one_le_lg hn2
  obtain ⟨w, hwdef⟩ : ∃ w, w = lg (k / e l) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = e l * n := ⟨_, rfl⟩
  rw [← hwdef] at hw
  rw [← hY] at hklg
  have hY1 : 1 ≤ Y := by nlinarith
  have hX : expVariablesA k n (e l) = (k : ℝ) ^ 2 * w * Y := by rw [expVariablesA, ← hwdef, hY]; ring
  have h8 : lg (8 * k / e l) ≤ 4 * w := by
    rw [lg_eight_div (by linarith) he0, ← hwdef]
    linarith
  have hkw : 3 ≤ (k : ℝ) * w := by nlinarith
  have hYX : Y ≤ (k : ℝ) ^ 2 * w * Y := le_mul_of_one_le_left (by linarith) (by nlinarith)
  have hkwX : (k : ℝ) * w ≤ (k : ℝ) ^ 2 * w * Y := by
    have : (k : ℝ) * w * 1 ≤ (k : ℝ) * w * (k * Y) := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
    calc (k : ℝ) * w = (k : ℝ) * w * 1 := (mul_one _).symm
      _ ≤ (k : ℝ) * w * (k * Y) := this
      _ = (k : ℝ) ^ 2 * w * Y := by ring
  have hX0 : 0 ≤ (k : ℝ) ^ 2 * w * Y := by linarith
  -- the outputs
  have hout : (needOutputs S k r (Q.idx l) n : ℝ) ≤ ((14 * A₁ : ℕ) : ℝ) * ((k : ℝ) ^ 2 * w * Y) := by
    have hb0 : 0 ≤ ((14 * A₁ : ℕ) : ℝ) * ((k : ℝ) ^ 2 * w * Y) := mul_nonneg (Nat.cast_nonneg _) hX0
    refine le_trans ?_ (Nat.floor_le hb0)
    have : needOutputs S k r (Q.idx l) n ≤ ⌊((14 * A₁ : ℕ) : ℝ) * ((k : ℝ) ^ 2 * w * Y)⌋₊ := by
      unfold needOutputs
      refine foldr_max_zero_le fun x hx => ?_
      obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.1 hx
      obtain ⟨hΔ2, hΔo⟩ := of_mem_deltas hΔ
      obtain ⟨d1, d2, -, -, -⟩ := hb k n Δ r (e l) hnb hk hk4 hen he1 hr1 hr2 hΔ2 hΔo
      refine Nat.le_floor ((hA k n l Δ hna hl hk hk4 hΔ2 d2).trans ?_)
      have g1 : lg Δ ≤ 14 * (k * w) := by
        have : 3 * (k : ℝ) * lg (8 * k / e l) ≤ 3 * k * (4 * w) := mul_le_mul_of_nonneg_left h8 (by linarith)
        linarith
      calc (A₁ : ℝ) * e l * k * n * lg Δ ≤ (A₁ : ℝ) * e l * k * n * (14 * (k * w)) := mul_le_mul_of_nonneg_left g1 (by positivity)
        _ = ((14 * A₁ : ℕ) : ℝ) * ((k : ℝ) ^ 2 * w * Y) := by rw [hY]; push_cast; ring
    exact_mod_cast this
  -- the walk
  have hwalk : (needWalk k r n : ℝ) ≤ ((2 + 5 * c : ℕ) : ℝ) * ((k : ℝ) ^ 2 * w * Y) := by
    refine (hc k n r hk hn2 hr1p hr2p).trans ?_
    have g1 : ((epsOf r : ℚ) : ℝ) * n ≤ 2 * Y := by
      rw [hY]
      have := mul_le_mul_of_nonneg_right hε2 hn0
      linarith
    have g2 : lg (8 * k / ((epsOf r : ℚ) : ℝ)) ≤ 4 * w :=
      (lg_mono (div_pos (by linarith) (lt_of_lt_of_le he0 hε1)) (div_le_div_of_nonneg_left (by linarith) he0 hε1)).trans h8
    have g3 : (c : ℝ) * k * (lg n + lg (8 * k / ((epsOf r : ℚ) : ℝ))) ≤ (c : ℝ) * (Y + 4 * (k * w)) := by
      have : (k : ℝ) * (lg n + lg (8 * k / ((epsOf r : ℚ) : ℝ))) ≤ Y + 4 * (k * w) := by
        have := mul_le_mul_of_nonneg_left g2 (by linarith : (0 : ℝ) ≤ k)
        linarith
      calc (c : ℝ) * k * (lg n + lg (8 * k / ((epsOf r : ℚ) : ℝ))) = (c : ℝ) * (k * (lg n + lg (8 * k / ((epsOf r : ℚ) : ℝ)))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg c)
    have g4 : (c : ℝ) * (Y + 4 * (k * w)) ≤ (c : ℝ) * (5 * ((k : ℝ) ^ 2 * w * Y)) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg c)
    push_cast
    linarith
  rw [hX]
  push_cast at hout hwalk ⊢
  linarith
end RecursionToBound
