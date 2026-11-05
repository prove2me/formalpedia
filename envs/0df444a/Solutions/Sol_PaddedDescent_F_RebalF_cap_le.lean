-- Prove2me | solution 1 for PaddedDescent.F.RebalF.cap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:56:35.88322+00:00
-- url     : https://prove2.me/submissions/449a222f-8e13-41ca-a9f6-e8150cbf06ce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {C : Type}
namespace PaddedDescent.F.RebalF
theorem _root_.solution {F : FNet C} {c : C} {g : ℕ} {N : Network (Fin g) (List Bool) (List Bool)} {P B : ℕ}
    (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B) {a b : Fin g} (hab : a ≠ b) : F.toP.cap c a b ≤ P := by
  rw [← hN.c_eq a b hab]
  exact (Finset.single_le_sum (f := fun b => N.c a b) (fun _ _ => Nat.zero_le _)
    (Finset.mem_erase.2 ⟨hab.symm, mem_univ b⟩)).trans (hS.sum_c a)
end PaddedDescent.F.RebalF
