-- Prove2me | solution 1 for ThmVariables.partAFromThePaddingString
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:38:12.533422+00:00
-- url     : https://prove2.me/submissions/e07ee0d2-fbdf-4753-8959-169797a23f9e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_ThmVariables_Bound
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ThmVariables_PartA
import Theorems.Thm_ThmVariables_numberBetween_cut
import Theorems.Thm_ThmVariables_conclusion_of_cut
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_hyp


set_option autoImplicit false
section
section
open ThmVariables
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms
open Sat3 (CNF)
namespace ThmVariables
theorem _root_.solution : PartAFromThePaddingString := by
  intro hSolver hVariablesA K e C₀ kf num E hyp
  obtain ⟨Idx, inst, S, C₀', Q, hS, hK⟩ := hSolver K e C₀ kf num E hyp
  obtain ⟨M, C', hf, hM⟩ := hVariablesA Idx S (cutNumber K num) C₀' Q hS (cutFraction num) (numberBetween_cut Q hyp.number.1 hK)
  exact ⟨M, 2 * C', hf, conclusion_of_cut Q hyp.levels hyp.number hK hM⟩
end ThmVariables
