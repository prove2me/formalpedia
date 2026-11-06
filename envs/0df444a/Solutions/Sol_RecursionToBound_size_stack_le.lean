-- Prove2me | solution 1 for RecursionToBound.size_stack_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:01:22.912228+00:00
-- url     : https://prove2.me/submissions/bfcf05f5-0df8-4b59-8b12-f37fad5637ee

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
theorem _root_.solution (k τ n m : ℕ) : Nat.size (stackLenCU k τ n m) ≤ 2 * k * Nat.size τ + 2 * k + Nat.size m + 5 * Nat.size n + 36 := by
  unfold stackLenCU bsumU
  have f1 := size_add_le ((τ ^ (2 * k) * n + 1) * (2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8) + 3 * n) 16
  have f2 := size_add_le ((τ ^ (2 * k) * n + 1) * (2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8)) (3 * n)
  have f3 := ClauseBound.Gen.Rate.size_mul_le (τ ^ (2 * k) * n + 1) (2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8)
  have f4 := ClauseBound.Gen.Rate.size_mul_le 3 n
  have a1 := size_add_le (τ ^ (2 * k) * n) 1
  have a2 := ClauseBound.Gen.Rate.size_mul_le (τ ^ (2 * k)) n
  have a3 := size_pow_le τ (2 * k)
  have g1 := size_add_le (2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10)) 8
  have g2 := size_add_le (2 ^ k * m * (k * (3 * n + 5) + 10)) (2 * n * (2 * (3 * n + 5) + 10))
  have h1 := ClauseBound.Gen.Rate.size_mul_le (2 ^ k * m) (k * (3 * n + 5) + 10)
  have h2 := ClauseBound.Gen.Rate.size_mul_le (2 ^ k) m
  have h3 : Nat.size (2 ^ k) = k + 1 := Nat.size_pow
  have h4 := size_add_le (k * (3 * n + 5)) 10
  have h5 := ClauseBound.Gen.Rate.size_mul_le k (3 * n + 5)
  have h6 := size_add_le (3 * n) 5
  have p1 := ClauseBound.Gen.Rate.size_mul_le (2 * n) (2 * (3 * n + 5) + 10)
  have p2 := ClauseBound.Gen.Rate.size_mul_le 2 n
  have p3 := size_add_le (2 * (3 * n + 5)) 10
  have p4 := ClauseBound.Gen.Rate.size_mul_le 2 (3 * n + 5)
  have hk := size_le_self k
  have c1 : Nat.size 1 ≤ 1 := Nat.size_le.2 (by norm_num)
  have c2 : Nat.size 2 ≤ 2 := Nat.size_le.2 (by norm_num)
  have c3 : Nat.size 3 ≤ 2 := Nat.size_le.2 (by norm_num)
  have c5 : Nat.size 5 ≤ 3 := Nat.size_le.2 (by norm_num)
  have c8 : Nat.size 8 ≤ 4 := Nat.size_le.2 (by norm_num)
  have c10 : Nat.size 10 ≤ 4 := Nat.size_le.2 (by norm_num)
  have c16 : Nat.size 16 ≤ 5 := Nat.size_le.2 (by norm_num)
  omega
end RecursionToBound
