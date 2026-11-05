-- Prove2me | solution 1 for PaddedDescent.F.Mark.InvS.size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:55:40.387766+00:00
-- url     : https://prove2.me/submissions/043b4bcc-695b-4468-8fcd-9619dfe7df9b

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
import Theorems.Thm_PaddedDescent_F_Mark_Layers_size_step
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open Layers
namespace PaddedDescent.F.Mark
namespace InvS
theorem _root_.solution {n w : ℕ} {Λ : Fml} {rest : List Fml} (h : InvS n w Λ rest) :
    3 * rest.flatten.length ≤ 2 * (rest.flatten.length + Λ.length) + 5 := by
  unfold InvS at h
  have h1 : 3 ^ rest.flatten.length * 2 ^ w ≤ 2 ^ (rest.flatten.length + Λ.length + 1) * 2 ^ w := by
    rw [← pow_add]
    refine le_trans (Nat.le_add_left _ _) (h.trans (le_of_eq ?_))
    congr 1; omega
  have h2 := Nat.le_of_mul_le_mul_right h1 (by positivity)
  have := size_step _ _ h2
  omega
end InvS
end PaddedDescent.F.Mark
