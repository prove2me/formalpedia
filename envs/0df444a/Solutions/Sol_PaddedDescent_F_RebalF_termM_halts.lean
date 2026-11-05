-- Prove2me | solution 1 for PaddedDescent.F.RebalF.termM_halts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:11:17.461216+00:00
-- url     : https://prove2.me/submissions/7c57e4f7-b52c-4368-a65f-b8d9a90adebc

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
import Theorems.Thm_PaddedDescent_F_RebalF_halts_sumRange
import Theorems.Thm_PaddedDescent_F_RebalF_halts_ite
import Theorems.Thm_PaddedDescent_F_RebalF_halts_free
import Theorems.Thm_Groundwork_Stepped_const_runs
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_Stepped_mul2_runs


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {C : Type}
variable [HasSize C]
namespace PaddedDescent.F.RebalF
theorem _root_.solution (K g : ℕ) (F : FNet C) (u : (X0 C × ℕ) × ℕ) : Halts (termM K g F.toP) u (termP K g F u) := by
  unfold termM termP psiM
  refine halts_ite ⟨_, _, const_runs _ _⟩ (halts_ite (halts_free _ _ _) (halts_ite (halts_sumRange fun y _ => ?_)
    (halts_free _ _ _)))
  exact ⟨_, _, mul2_runs (mapIn_runs (freeM_runs F.f _)) (mapIn_runs (freeM_runs F.f _))⟩
end PaddedDescent.F.RebalF
