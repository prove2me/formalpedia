-- Prove2me | solution 1 for PaddedDescent.F.RebalF.termF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:07:56.592203+00:00
-- url     : https://prove2.me/submissions/683a13e5-299f-48d5-a3b7-e9ce949d19d4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_sumF_eq
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {C : Type}
namespace PaddedDescent.F.RebalF
theorem _root_.solution {pad : U} {K g : ℕ} {F : FNet C} {u : (X0 C × ℕ) × ℕ}
    (h : isW g u = false → nLab g F.toP u ≤ pad.length) : termF pad K g F u = termP K g F u := by
  unfold termF termP
  cases h2 : isW g u with
  | true => rfl
  | false => rw [sumF_eq (h h2)]
end PaddedDescent.F.RebalF
