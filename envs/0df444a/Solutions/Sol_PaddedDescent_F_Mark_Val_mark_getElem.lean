-- Prove2me | solution 1 for PaddedDescent.F.Mark.Val.mark_getElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:58.405725+00:00
-- url     : https://prove2.me/submissions/7793fa17-58fd-4eae-91b3-135262d417c3

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
import Theorems.Thm_PaddedDescent_F_Mark_Val_nodup_tch
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}
namespace PaddedDescent.F.Mark.Val
theorem _root_.solution (a : ℕ) (z : List Bool) {t : ℕ} (h : t < (tch g n Ls a).length) :
    mark g n Ls a z (tch g n Ls a)[t] = z.getD (qv g n + t) false := by
  unfold mark
  rw [(nodup_tch a).idxOf_getElem]
end PaddedDescent.F.Mark.Val
