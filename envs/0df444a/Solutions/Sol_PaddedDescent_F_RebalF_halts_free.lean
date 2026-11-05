-- Prove2me | solution 1 for PaddedDescent.F.RebalF.halts_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:07:55.637906+00:00
-- url     : https://prove2.me/submissions/0cb0f4ff-c1b3-4ab6-99ea-50c5550c753a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_PaddedDescent_F_RebalF_freeM_runs
import Theorems.Thm_Groundwork_Stepped_mapIn_runs


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {α β : Type}
namespace PaddedDescent.F.RebalF
theorem _root_.solution {γ : Type} (q : α → γ) (f : γ → β) (a : α) : Halts (mapIn q (freeM f)) a (f (q a)) :=
  ⟨_, _, mapIn_runs (freeM_runs f (q a))⟩
end PaddedDescent.F.RebalF
