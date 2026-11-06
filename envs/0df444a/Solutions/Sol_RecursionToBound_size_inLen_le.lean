-- Prove2me | solution 1 for RecursionToBound.size_inLen_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:57:56.561395+00:00
-- url     : https://prove2.me/submissions/b7545a58-67b2-4d68-afcf-17259a17506c

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
import Theorems.Thm_ClauseBound_Gen_Rate_size_add_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_le_self
import Theorems.Thm_ClauseBound_Gen_Rate_size_mul_le
import Theorems.Thm_ClauseBound_Gen_Rate_size_pow_le
import Theorems.Thm_ClauseBound_ParityChecks_size_mul_le
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_VariableBound_Net_Main_size


set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen.Rate ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution (k n : ℕ) : Nat.size (inLen k n) ≤ k * Nat.size n + 4 * k + Nat.size n + 5 := by
  unfold inLen
  have m1 := ClauseBound.Gen.Rate.size_mul_le (k * 2 ^ k + 1) ((n + 2) ^ (k + 1))
  have m2 := size_add_le (k * 2 ^ k) 1
  have m3 := ClauseBound.Gen.Rate.size_mul_le k (2 ^ k)
  have m4 := size_pow_le (n + 2) (k + 1)
  have m5 := size_add_le n 2
  have h3 : Nat.size (2 ^ k) = k + 1 := Nat.size_pow
  have hk := size_le_self k
  have c1 : Nat.size 1 ≤ 1 := Nat.size_le.2 (by norm_num)
  have c2 : Nat.size 2 ≤ 2 := Nat.size_le.2 (by norm_num)
  have b : (k + 1) * Nat.size (n + 2) ≤ k * Nat.size n + 2 * k + Nat.size n + 2 := by
    calc (k + 1) * Nat.size (n + 2) ≤ (k + 1) * (Nat.size n + 2) := Nat.mul_le_mul_left _ (by omega)
      _ = k * Nat.size n + 2 * k + Nat.size n + 2 := by ring
  omega
end RecursionToBound
