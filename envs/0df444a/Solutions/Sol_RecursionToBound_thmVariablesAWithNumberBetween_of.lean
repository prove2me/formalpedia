-- Prove2me | solution 1 for RecursionToBound.thmVariablesAWithNumberBetween_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:52:29.693537+00:00
-- url     : https://prove2.me/submissions/42631b70-5daa-4691-abaa-7ed80c40dbde

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_RecursionToBound_Exponent
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_Wrap_Sim
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_RecursionToBound_End

set_option autoImplicit false
section
section
open RecursionToBound
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End UniformInK Wrap MainTheoremForms PairsToBound VariableBound.Paper
open Sat3 (CNF)
namespace RecursionToBound
theorem _root_.solution (h : ThmVariablesAForEveryMachine) : ThmVariablesAWithNumberBetween := by
  intro Idx _ S e C₀ Q hS num hnum
  obtain ⟨n₀, hn₀⟩ := h Idx S e C₀ Q hS num hnum
  obtain ⟨⟨M, q, hf, hM⟩, hall⟩ := hn₀ n₀ le_rfl
  obtain ⟨C', hC'⟩ := hall M q hM
  exact ⟨M, C', hf, hC'⟩
end RecursionToBound
