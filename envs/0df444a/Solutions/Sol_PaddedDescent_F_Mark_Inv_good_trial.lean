-- Prove2me | solution 1 for PaddedDescent.F.Mark.Inv.good_trial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:04:48.160284+00:00
-- url     : https://prove2.me/submissions/177cb7b5-2012-4ad0-95e2-c9255463a935

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_PaddedDescent_F_MarkLayers
import Theorems.Thm_PaddedDescent_F_Mark_InvS_nvio_lt
import Theorems.Thm_PaddedDescent_F_Mark_Inv_good
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers
namespace PaddedDescent.F.Mark
namespace Inv
theorem _root_.solution {n w : ℕ} (C : Cl) {Λ L : Fml} {rest : List Fml} (h : Inv n w (Λ :: L :: rest))
    (hl : ((Λ :: L :: rest).getLastD []).length ≤ w) : Good n w ((C :: Λ) :: L :: rest) := by
  refine ⟨fun σ hs => ?_, (h.good hl).2⟩
  have h1 := h.1.nvio_lt σ hs
  rw [nvio_cons]
  split_ifs <;> omega
end Inv
end PaddedDescent.F.Mark
