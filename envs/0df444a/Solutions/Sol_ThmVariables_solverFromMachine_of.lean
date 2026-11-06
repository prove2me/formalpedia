-- Prove2me | solution 1 for ThmVariables.solverFromMachine_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:57:59.907277+00:00
-- url     : https://prove2.me/submissions/799077fc-028f-4a30-8a2b-98271698fa15

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_ThmVariables_Bound
import Definitions.Def_ThmVariables_PartA
import Definitions.Def_ThmVariables_EveryMachine
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_hyp


set_option autoImplicit false
section
section
open ThmVariables
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms
namespace ThmVariables
theorem _root_.solution (h : SolverOfMachineLevels) : SolverFromMachine := by
  intro K e C₀ kf num E hyp
  obtain ⟨inst⟩ := hyp.steps
  obtain ⟨hP, Q, -, hK, -⟩ := h E K e C₀ kf num hyp.solves hyp.levels hyp.computesK hyp.number
  exact ⟨_, inferInstance, solverOfMachine E num C₀, 2 * C₀ + 1, Q, hP, hK⟩
end ThmVariables
