-- Prove2me | solution 1 for RecursionToBound.six_test
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:50:47.95044+00:00
-- url     : https://prove2.me/submissions/2cdcfe47-7142-420b-8a28-12d66fbc2bf5

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

set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.ParityChecks UniformInK VariableBound.Net MainTheoremForms VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution {C₀ k ℓ : ℕ} (hC : 1 ≤ C₀) (hk : 1 ≤ k) (h1 : (520200 * C₀ ^ 4) ^ 2 ≤ ℓ) (h2 : k ^ 4 ≤ ℓ) : 2 * (102 * C₀ * (4 * k * C₀ + 1)) ^ 2 ≤ ℓ := by
  have a : 4 * k * C₀ + 1 ≤ 5 * k * C₀ := by nlinarith [Nat.mul_pos hk hC]
  have b : 2 * (102 * C₀ * (4 * k * C₀ + 1)) ^ 2 ≤ 2 * (102 * C₀ * (5 * k * C₀)) ^ 2 :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ a) 2)
  have c : 2 * (102 * C₀ * (5 * k * C₀)) ^ 2 = 520200 * C₀ ^ 4 * k ^ 2 := by ring
  have d : (520200 * C₀ ^ 4 * k ^ 2) ^ 2 ≤ ℓ ^ 2 := by
    calc (520200 * C₀ ^ 4 * k ^ 2) ^ 2 = (520200 * C₀ ^ 4) ^ 2 * k ^ 4 := by ring
      _ ≤ ℓ * ℓ := Nat.mul_le_mul h1 h2
      _ = ℓ ^ 2 := by ring
  have f := (Nat.pow_le_pow_iff_left (by norm_num)).1 d
  omega
end RecursionToBound
