-- Prove2me | solution 1 for PaddedDescent.F.RebalF.betaC_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:12:34.423527+00:00
-- url     : https://prove2.me/submissions/bbc05009-d957-49f0-9a01-f8112e418bab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_Groundwork_Colouring_beta_le
import Theorems.Thm_Groundwork_Prog_NetE_Pc_le
import Theorems.Thm_Groundwork_Prog_NetE_Uc_eq


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {C : Type}
namespace PaddedDescent.F.RebalF
theorem _root_.solution {F : FNet C} {c : C} {K g : ℕ} {N : Network (Fin g) (List Bool) (List Bool)} {P B : ℕ}
    (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B) : K ^ 3 * betaC K g F.toP c ≤ K ^ 3 + K * N.U + g * P := by
  have h1 := Colouring.beta_le K g (Uc g F.toP c) (Pc g F.toP c)
  rw [Uc_eq F.toP hN] at h1
  have h2 : g * Pc g F.toP c ≤ g * P := Nat.mul_le_mul_left _ (Pc_le F.toP hN hS)
  rw [betaC, Uc_eq F.toP hN]
  omega
end PaddedDescent.F.RebalF
