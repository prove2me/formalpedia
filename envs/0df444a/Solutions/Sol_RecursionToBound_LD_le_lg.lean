-- Prove2me | solution 1 for RecursionToBound.LD_le_lg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:45.473984+00:00
-- url     : https://prove2.me/submissions/4536658f-7c6a-438e-a366-91168017d5c1

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

set_option autoImplicit false
section
section
open RecursionToBound
open Finset ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution {Δ n : ℕ} (hn : 1 ≤ n) (h : Δ ≤ n) : (LD Δ : ℝ) ≤ lg n + 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : 0 ≤ lg n := Real.logb_nonneg one_lt_two (by exact_mod_cast hn)
  have h1 : (n : ℝ) ≤ (2 : ℝ) ^ ⌈lg n⌉₊ := by
    have e : (n : ℝ) = (2 : ℝ) ^ lg n := (Real.rpow_logb two_pos (by norm_num) hn0).symm
    calc (n : ℝ) = (2 : ℝ) ^ lg n := e
      _ ≤ (2 : ℝ) ^ ((⌈lg n⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)
      _ = (2 : ℝ) ^ ⌈lg n⌉₊ := Real.rpow_natCast _ _
  have h2 : n ≤ 2 ^ ⌈lg n⌉₊ := by exact_mod_cast h1
  have h3 : 2 * Δ ≤ 2 ^ (⌈lg n⌉₊ + 1) := by
    rw [pow_succ]
    omega
  have h4 : LD Δ ≤ ⌈lg n⌉₊ + 1 := Nat.clog_le_of_le_pow h3
  have h5 : ((⌈lg n⌉₊ : ℕ) : ℝ) < lg n + 1 := Nat.ceil_lt_add_one hL0
  have h6 : (LD Δ : ℝ) ≤ ((⌈lg n⌉₊ : ℕ) : ℝ) + 1 := by exact_mod_cast h4
  linarith
end RecursionToBound
