-- Prove2me | solution 1 for RecursionToBound.of_mem_deltas
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:50:52.192201+00:00
-- url     : https://prove2.me/submissions/1b939a2d-5da9-4c01-bf45-6b1ec1fff8a0

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

set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen.Rate ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution {k n Δ : ℕ} {r : ℕ × ℕ} (h : Δ ∈ deltas k r n) : 2 ≤ Δ ∧ Δ ≤ occBound k r := by
  unfold deltas at h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
  have := List.mem_range.1 hj
  omega
end RecursionToBound
