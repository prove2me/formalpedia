-- Prove2me | solution 1 for VariableBound.VariablesA.stepSparsifySmall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:33.537407+00:00
-- url     : https://prove2.me/submissions/3cd72fbf-5d49-4a19-9a3f-d15423ec53c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Theorems.Thm_VariableBound_VariablesA_lg_le_self
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_VariablesA_lg_div_facts


set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork Turing PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End MainTheoremForms
open Sat3 (CNF)
namespace VariableBound.VariablesA
theorem _root_.solution : StepSparsifySmallStmt := by
  intro C₀ n₁
  refine ⟨n₁ ^ C₀, fun k n x hn2 hn hk hx hx1 => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hy1 : 1 ≤ MainTheoremForms.lg n := by
    rw [MainTheoremForms.lg, Real.le_logb_iff_rpow_le (by norm_num) hn0, Real.rpow_one]
    exact_mod_cast hn2
  have hy0 : 0 < MainTheoremForms.lg n := by linarith
  have hyn : MainTheoremForms.lg n ≤ (n₁ : ℝ) := (lg_le_self n).trans (by exact_mod_cast hn.le)
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h1 : 1 / (n₁ : ℝ) ^ C₀ ≤ x := le_trans (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hy0.le hyn _)) hx
  have hp : (0 : ℝ) < (n₁ : ℝ) ^ C₀ := pow_pos (by linarith) _
  have h2 : 1 ≤ (n₁ : ℝ) ^ C₀ * x := by
    rw [div_le_iff₀ hp] at h1
    linarith
  obtain ⟨w1, w2⟩ := lg_div_facts hk hx0 hx1
  have hw : 1 ≤ MainTheoremForms.lg (k / x) := w1.trans w2
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by linarith)
  have h3 : 1 ≤ (k : ℝ) ^ 2 * MainTheoremForms.lg (k / x) := one_le_mul_of_one_le_of_one_le hk2 hw
  have h4 : 1 ≤ ((n₁ : ℝ) ^ C₀ * x) * ((k : ℝ) ^ 2 * MainTheoremForms.lg (k / x)) := one_le_mul_of_one_le_of_one_le h2 h3
  have h5 : (n : ℝ) ≤ ((n₁ ^ C₀ : ℕ) : ℝ) * expVariablesA k n x := by
    calc (n : ℝ) = n * 1 := (mul_one _).symm
      _ ≤ n * (((n₁ : ℝ) ^ C₀ * x) * ((k : ℝ) ^ 2 * MainTheoremForms.lg (k / x))) := mul_le_mul_of_nonneg_left h4 hn0.le
      _ = _ := by rw [expVariablesA]; push_cast; ring
  refine ⟨h5, ?_⟩
  have h6 : 1 ≤ ((n₁ : ℝ) ^ C₀ * x) * MainTheoremForms.lg (k / x) := one_le_mul_of_one_le_of_one_le h2 hw
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  calc (k : ℝ) * MainTheoremForms.lg n ≤ (k : ℝ) ^ 2 * n := mul_le_mul hkk (lg_le_self n) hy0.le (by positivity)
    _ = (k : ℝ) ^ 2 * n * 1 := (mul_one _).symm
    _ ≤ (k : ℝ) ^ 2 * n * (((n₁ : ℝ) ^ C₀ * x) * MainTheoremForms.lg (k / x)) := mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = _ := by rw [expVariablesA]; push_cast; ring
end VariableBound.VariablesA
