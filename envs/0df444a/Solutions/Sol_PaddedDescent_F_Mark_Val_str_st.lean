-- Prove2me | solution 1 for PaddedDescent.F.Mark.Val.str_st
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:56:16.09424+00:00
-- url     : https://prove2.me/submissions/6a505f93-a495-41e4-afa1-0b528b363e81

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
import Theorems.Thm_PaddedDescent_F_Mark_Val_mem_tch_of_mem_tst
import Theorems.Thm_PaddedDescent_F_Mark_Val_mark_st
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}
namespace PaddedDescent.F.Mark.Val
theorem _root_.solution (σ : ℕ → Bool) (P : Finset ℕ) (a a' i : ℕ) :
    str g n Ls a a' i (st g n Ls σ P a) = (tst g n Ls a a' i).map fun e => decide (e ∈ P) := by
  unfold str
  exact List.map_congr_left fun e he => mark_st σ P (mem_tch_of_mem_tst he)
end PaddedDescent.F.Mark.Val
