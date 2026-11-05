-- Prove2me | solution 1 for PaddedDescent.F.Mark.Val.stMarkVal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:33:35.125273+00:00
-- url     : https://prove2.me/submissions/3e2ddf4c-8f5c-4894-81c2-e3a959d0e7ec

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
import Theorems.Thm_PaddedDescent_F_Mark_Val_markVal
import Theorems.Thm_PaddedDescent_F_Mark_Val_eq_replicate
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}
namespace PaddedDescent.F.Mark.Val
theorem _root_.solution (hLen : StEncLen) (hCat : StEncInj) : StMarkVal := by
  intro k gu nu βu bu Ls y hg h0 hb hw
  have e : (((gu, nu, βu, bu), (Ls, y)) : MCtx) = ctx gu.length nu.length βu.length bu.length Ls y := by
    rw [ctx, ← eq_replicate, ← eq_replicate, ← eq_replicate, ← eq_replicate]
  rw [e]
  exact markVal hLen hCat hg h0 hb hw
end PaddedDescent.F.Mark.Val
