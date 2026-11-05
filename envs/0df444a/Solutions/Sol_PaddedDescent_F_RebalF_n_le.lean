-- Prove2me | solution 1 for PaddedDescent.F.RebalF.n_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:07:57.56617+00:00
-- url     : https://prove2.me/submissions/581a1c20-6b52-499c-90ee-2a09848bcc22

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_PaddedDescent_F_RebalF
import Theorems.Thm_Groundwork_card_words


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset
variable {C : Type}
namespace PaddedDescent.F.RebalF
theorem _root_.solution {F : FNet C} {c : C} {g : ℕ} {N : Network (Fin g) (List Bool) (List Bool)} {P B : ℕ}
    (hN : F.toP.Presents c N 0 0) (hS : N.Sized P B) (a : Fin g) : F.toP.n c a ≤ P := by
  have := hS.card_S a
  rw [hN.S_eq, card_words] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
end PaddedDescent.F.RebalF
