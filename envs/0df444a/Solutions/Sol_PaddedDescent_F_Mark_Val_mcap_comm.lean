-- Prove2me | solution 1 for PaddedDescent.F.Mark.Val.mcap_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:00.615902+00:00
-- url     : https://prove2.me/submissions/4d48f76a-704b-417e-96af-4785ceeceb7d

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
import Theorems.Thm_PaddedDescent_F_Mark_Val_tst_comm
import Theorems.Thm_PaddedDescent_F_Mark_Val_mu_comm
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}
namespace PaddedDescent.F.Mark.Val
theorem _root_.solution (a a' : ℕ) : mcap g n β b Ls y a a' = mcap g n β b Ls y a' a := by
  unfold mcap
  refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
  rw [mu_comm, tst_comm]
end PaddedDescent.F.Mark.Val
