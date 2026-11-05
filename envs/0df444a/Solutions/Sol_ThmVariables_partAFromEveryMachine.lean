-- Prove2me | solution 1 for ThmVariables.partAFromEveryMachine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:08:11.764539+00:00
-- url     : https://prove2.me/submissions/3bc17eb4-2d6e-4c3a-9cb0-a687aa8e1079

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
theorem _root_.solution : PartAFromEveryMachine := by
  intro h K e C₀ kf num E hyp
  obtain ⟨inst⟩ := hyp.steps
  obtain ⟨n₀, hn₀⟩ := h K e C₀ kf num E hyp
  obtain ⟨⟨M, q, hf, hM⟩, hall⟩ := hn₀ n₀ le_rfl
  obtain ⟨C', hC'⟩ := hall M q hM
  exact ⟨M, C', hf, hC'⟩
end ThmVariables
