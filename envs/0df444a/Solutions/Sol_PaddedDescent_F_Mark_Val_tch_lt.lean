-- Prove2me | solution 1 for PaddedDescent.F.Mark.Val.tch_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:52:11.072341+00:00
-- url     : https://prove2.me/submissions/952c1b46-31a0-4f20-b2bb-3351beba9ee3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Definitions.Def_PaddedDescent_F_MarkVal
import Theorems.Thm_PaddedDescent_F_Mark_Val_tchB_iff
import Theorems.Thm_PaddedDescent_F_Mark_Val_clAt_mem
import Theorems.Thm_PaddedDescent_F_Mark_Val_div_qv_lt
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}
namespace PaddedDescent.F.Mark.Val
theorem _root_.solution (hg : 0 < g) (hW : WfL k n Ls) {e a : ℕ} (he : e < (cls Ls).length) (h : tchB g n Ls a e = true) : a < g := by
  obtain ⟨l, hl, rfl⟩ := tchB_iff.1 h
  obtain ⟨L, hL, hC⟩ := clAt_mem he
  exact div_qv_lt hg ((hW L hL _ hC).2.2 l hl)
end PaddedDescent.F.Mark.Val
