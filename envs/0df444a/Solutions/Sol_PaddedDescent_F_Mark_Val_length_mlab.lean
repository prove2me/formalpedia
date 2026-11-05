-- Prove2me | solution 1 for PaddedDescent.F.Mark.Val.length_mlab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:17.104682+00:00
-- url     : https://prove2.me/submissions/2b7782e4-9c1a-447f-a05e-559333bd6d61

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
import Theorems.Thm_PaddedDescent_F_Mark_Val_encLen
import Theorems.Thm_PaddedDescent_F_Mark_Val_prof_iff
import Theorems.Thm_PaddedDescent_F_Mark_Val_length_str
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.sum



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}
namespace PaddedDescent.F.Mark.Val
theorem _root_.solution (hLen : StEncLen) (h0 : 0 < b) {a a' : ℕ} (ha' : a' < g) (hne : a' ≠ a) {z : List Bool}
    (hz : prof g n Ls y a z = true) : (mlab g n β b Ls a a' z).length = mcap g n β b Ls y a a' := by
  unfold mlab mcap
  rw [encLen hLen β b h0 (fun i => str g n Ls a a' i z)]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  rw [(prof_iff.1 hz).2 a' ha' hne i (List.mem_range.1 hi), length_str]
end PaddedDescent.F.Mark.Val
