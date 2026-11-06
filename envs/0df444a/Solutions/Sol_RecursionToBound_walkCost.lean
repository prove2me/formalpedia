-- Prove2me | solution 1 for RecursionToBound.walkCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:08:02.133287+00:00
-- url     : https://prove2.me/submissions/cf841241-a6b3-4fe8-b7b1-84b7ea5e0c42

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
import Theorems.Thm_RecursionToBound_size_inLen_le
import Theorems.Thm_RecursionToBound_size_stack_le
import Theorems.Thm_ClauseBound_Alg_TopArith_size_le_two_logb
import Theorems.Thm_RecursionToBound_epsOf_le_one
import Theorems.Thm_RecursionToBound_epsOf_pos
import Theorems.Thm_SparsificationLemma_Cal_stAlpha
import Theorems.Thm_SparsificationLemma_Cal_stAlphaLe
import Theorems.Thm_VariableBound_Net_FitL_lg_mono
import Theorems.Thm_VariableBound_Net_Main_size
import Theorems.Thm_VariableBound_Paper_lg_mono
import Theorems.Thm_VariableBound_Paper_one_le_lg


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen.Rate ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution : WalkCost := by
  refine ⟨29, fun k n r hk hn h1 h2 => ?_⟩
  have hε0 := epsOf_pos h1 h2
  have hε1 := epsOf_le_one r
  have hε0' : (0 : ℝ) < ((epsOf r : ℚ) : ℝ) := by exact_mod_cast hε0
  have hε1' : ((epsOf r : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hε1
  obtain ⟨-, hα, -, -, -⟩ := Cal.stAlpha k (epsOf r) hk hε0 hε1
  have hαle := Cal.stAlphaLe k (epsOf r) hk hε0 hε1
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hL := one_le_lg hn
  have hw0 : 0 ≤ lg (8 * k / ((epsOf r : ℚ) : ℝ)) := by
    refine Real.logb_nonneg one_lt_two ?_
    rw [le_div_iff₀ hε0']
    linarith
  have ht : ((32 * Cal.alphaC k (epsOf r)).size : ℝ) ≤ 6 * lg (8 * k / ((epsOf r : ℚ) : ℝ)) := by
    have a1 := size_le_two_logb (32 * Cal.alphaC k (epsOf r)) (by omega)
    have a2 : lg ((32 * Cal.alphaC k (epsOf r) : ℕ) : ℝ) ≤ lg ((8 * (k : ℝ) / ((epsOf r : ℚ) : ℝ)) ^ 3) :=
      lg_mono (by exact_mod_cast (by omega : 0 < 32 * Cal.alphaC k (epsOf r))) (by push_cast; exact hαle)
    have a3 : lg ((8 * (k : ℝ) / ((epsOf r : ℚ) : ℝ)) ^ 3) = 3 * lg (8 * k / ((epsOf r : ℚ) : ℝ)) := by
      unfold lg
      rw [Real.logb_pow]
      norm_num
    unfold lg at a2 a3 ⊢
    linarith
  have hs : (n.size : ℝ) ≤ 2 * lg n := size_le_two_logb n hn
  have hceil : ((⌈epsOf r * (n : ℚ)⌉₊ : ℕ) : ℝ) ≤ ((epsOf r : ℚ) : ℝ) * n + 1 := by
    have a1 := Nat.ceil_lt_add_one (a := epsOf r * (n : ℚ)) (by positivity)
    have a2 : (((⌈epsOf r * (n : ℚ)⌉₊ : ℕ) : ℚ) : ℝ) < ((epsOf r * (n : ℚ) + 1 : ℚ) : ℝ) := by exact_mod_cast a1
    push_cast at a2
    exact a2.le
  have hst : Nat.size (stackLenCU k (32 * Cal.alphaC k (epsOf r)) n (inLen k n)) ≤
      2 * k * Nat.size (32 * Cal.alphaC k (epsOf r)) + k * Nat.size n + 6 * k + 6 * Nat.size n + 41 := by
    have a1 := size_stack_le k (32 * Cal.alphaC k (epsOf r)) n (inLen k n)
    have a2 := size_inLen_le k n
    omega
  have hst' : ((Nat.size (stackLenCU k (32 * Cal.alphaC k (epsOf r)) n (inLen k n)) : ℕ) : ℝ) ≤
      2 * (k : ℝ) * ((32 * Cal.alphaC k (epsOf r)).size : ℝ) + (k : ℝ) * (n.size : ℝ) + 6 * k + 6 * (n.size : ℝ) + 41 := by exact_mod_cast hst
  have b1 : (k : ℝ) * ((32 * Cal.alphaC k (epsOf r)).size : ℝ) ≤ k * (6 * lg (8 * k / ((epsOf r : ℚ) : ℝ))) := mul_le_mul_of_nonneg_left ht (by linarith)
  have b2 : (k : ℝ) * (n.size : ℝ) ≤ k * (2 * lg n) := mul_le_mul_of_nonneg_left hs (by linarith)
  have b3 : (k : ℝ) ≤ k * lg n := le_mul_of_one_le_right (by linarith) hL
  have b4 : 3 * lg n ≤ k * lg n := mul_le_mul_of_nonneg_right hk' (by linarith)
  have b5 : 0 ≤ (k : ℝ) * lg (8 * k / ((epsOf r : ℚ) : ℝ)) := mul_nonneg (by linarith) hw0
  unfold needWalk
  push_cast
  nlinarith
end RecursionToBound
