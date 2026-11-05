-- Prove2me | solution 1 for PaddedDescent.F.RebalF.mergedM_halts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:59.369168+00:00
-- url     : https://prove2.me/submissions/3b7e8950-b38b-407f-8be8-6b9326adb7e4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_PaddedDescent_F_RebalF_halts_sumRange
import Theorems.Thm_PaddedDescent_F_RebalF_halts_prodRange
import Theorems.Thm_PaddedDescent_F_RebalF_halts_ite
import Theorems.Thm_PaddedDescent_F_RebalF_termM_halts
import Theorems.Thm_Groundwork_Stepped_const_runs


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {C : Type}
variable [HasSize C]
namespace PaddedDescent.F.RebalF
theorem _root_.solution (K g : ℕ) (F : FNet C) (u : X0 C) : Halts (mergedM K g F.toP) u (mergedP K g F u) := by
  unfold mergedM mergedP
  exact halts_ite (halts_sumRange fun y _ => halts_prodRange fun i _ => termM_halts K g F ((u, y), i)) ⟨_, _, const_runs _ _⟩
end PaddedDescent.F.RebalF
