-- Prove2me | solution 1 for PaddedDescent.F.Mark.trunc_sub_trunc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:07:58.056696+00:00
-- url     : https://prove2.me/submissions/190bc551-0a79-498b-912b-bc237fac36c6

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
import Theorems.Thm_PaddedDescent_F_Mark_Inv_good
import Theorems.Thm_PaddedDescent_F_Mark_trunc_eq_XX
import Theorems.Thm_PaddedDescent_F_Mark_Inv_good_trial
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers
namespace PaddedDescent.F.Mark
theorem _root_.solution {n w : ℕ} (C : Cl) {Λ L : Fml} {rest : List Fml} (h : Inv n w (Λ :: L :: rest))
    (hl : ((Λ :: L :: rest).getLastD []).length ≤ w) :
    trunc n w ((C :: Λ) :: L :: rest) - trunc n w (Λ :: L :: rest) = (BB n C Λ (L :: rest) : ℤ) := by
  rw [trunc_eq_XX (h.good_trial C hl), trunc_eq_XX (h.good hl), XX_cons]
  push_cast; ring
end PaddedDescent.F.Mark
