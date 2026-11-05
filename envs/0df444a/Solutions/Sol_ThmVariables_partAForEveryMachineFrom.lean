-- Prove2me | solution 1 for ThmVariables.partAForEveryMachineFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:38:05.579276+00:00
-- url     : https://prove2.me/submissions/6746405a-d241-4a9a-bbf0-13957f057d8b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_ThmVariables_Bound
import Definitions.Def_ThmVariables_PartA
import Definitions.Def_ThmVariables_EveryMachine
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_hyp
import Theorems.Thm_ThmVariables_conclusion_of_cut
import Theorems.Thm_ThmVariables_numberBetween_cut


set_option autoImplicit false
section
section
open ThmVariables
open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms
namespace ThmVariables
theorem _root_.solution : PartAForEveryMachineFrom := by
  intro hB hVariablesA K e C₀ kf num E _ hyp
  obtain ⟨hP, Q, -, hK, hpick⟩ := hB E K e C₀ kf num hyp.solves hyp.levels hyp.computesK hyp.number
  obtain ⟨n₀, hn₀⟩ := hVariablesA _ (solverOfMachine E num C₀) (cutNumber K num) (2 * C₀ + 1) Q hP (cutFraction num) (numberBetween_cut Q hyp.number.1 hK)
  refine ⟨n₀, fun n₁ hn₁ => ?_⟩
  obtain ⟨h1, h2⟩ := hn₀ n₁ hn₁
  rw [hpick] at h1 h2
  refine ⟨h1, fun M q hM => ?_⟩
  obtain ⟨C', hC'⟩ := h2 M q hM
  exact ⟨2 * C', conclusion_of_cut Q hyp.levels hyp.number hK hC'⟩
end ThmVariables
