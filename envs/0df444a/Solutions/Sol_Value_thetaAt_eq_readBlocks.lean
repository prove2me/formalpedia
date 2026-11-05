-- Prove2me | solution 1 for Value.thetaAt_eq_readBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:54:32.705964+00:00
-- url     : https://prove2.me/submissions/cb7b27c4-600e-4847-af21-c8c125238db0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_pr_of_lt
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
namespace Value
theorem _root_.solution (hSB : StSameBlock) (Np : Procs C) (c : C) (hK0 : 0 < K) (x : ℕ) (Λ : Fin K × Fin K → List Bool) {a b : Fin g}
    (hne : Paper.grouping hK0 x a ≠ Paper.grouping hK0 x b) :
    thetaAt Np.toPaperNetwork c hK0 x (star Λ (Paper.grouping hK0 x a)) a b = readBlocks Np c hK0 x Λ (pr a b) := by
  have hab : a ≠ b := fun e => hne (e ▸ rfl)
  rcases lt_or_gt_of_ne hab with h | h
  · rw [(pr_of_lt h).1]
    exact (if_pos ⟨h, hne⟩).symm
  · rw [(pr_of_lt h).2, hSB C g K Np c hK0 x Λ a b hne]
    exact (if_pos ⟨h, hne.symm⟩).symm
end Value
