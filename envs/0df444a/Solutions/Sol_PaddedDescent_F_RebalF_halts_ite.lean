-- Prove2me | solution 1 for PaddedDescent.F.RebalF.halts_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:15:50.113174+00:00
-- url     : https://prove2.me/submissions/75e7c469-707e-47cb-a77a-432b525e39fb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_Groundwork_Stepped_ite_runs_false
import Theorems.Thm_Groundwork_Stepped_ite_runs_true


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {α β : Type}
namespace PaddedDescent.F.RebalF
theorem _root_.solution {p : α → Bool} {M N : Stepped α β} {a : α} {b c : β} (h1 : Halts M a b) (h2 : Halts N a c) :
    Halts (Stepped.ite p M N) a (bif p a then b else c) := by
  obtain ⟨T, S, h1⟩ := h1
  obtain ⟨T', S', h2⟩ := h2
  cases hp : p a with
  | true => exact ⟨_, _, ite_runs_true hp h1⟩
  | false => exact ⟨_, _, ite_runs_false hp h2⟩
end PaddedDescent.F.RebalF
