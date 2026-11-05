-- Prove2me | solution 1 for PaddedDescent.F.RebalF.halts_prodRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:07:52.740242+00:00
-- url     : https://prove2.me/submissions/81efce8a-e677-4969-85da-6f7d63d4295d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_prodRange_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {α β : Type}
namespace PaddedDescent.F.RebalF
theorem _root_.solution [HasSize α] {N : α → ℕ} {M : Stepped (α × ℕ) ℤ} {a : α} {v : ℕ → ℤ}
    (h : ∀ y, y < N a → Halts M (a, y) (v y)) : Halts (prodRange N M) a (∏ y ∈ range (N a), v y) := by
  choose! t S hr using h
  exact ⟨_, _, prodRange_runs t v (((range (N a)).sup fun y => (v y).natAbs) + 1) ((range (N a)).sup S) (by omega)
    (fun y hy => (hr y hy).mono le_rfl (Finset.le_sup (f := S) (mem_range.2 hy)))
    (fun y hy => (Finset.le_sup (f := fun y => (v y).natAbs) (mem_range.2 hy)).trans (Nat.le_succ _))⟩
end PaddedDescent.F.RebalF
