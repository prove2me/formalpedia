-- Prove2me | solution 1 for PaddedDescent.F.Mark.Val.mem_tch_of_mem_tst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:50:54.529767+00:00
-- url     : https://prove2.me/submissions/0235d531-b336-43a1-ae6d-57bf0d865578

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
import Theorems.Thm_PaddedDescent_F_Mark_Val_mem_tch
import Theorems.Thm_PaddedDescent_F_Mark_Val_linkB_iff
import Theorems.Thm_PaddedDescent_F_Mark_Val_mem_tst
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}
namespace PaddedDescent.F.Mark.Val
theorem _root_.solution {a b i e : ℕ} (h : e ∈ tst g n Ls a b i) : e ∈ tch g n Ls a := by
  obtain ⟨h1, _, h3⟩ := mem_tst.1 h
  obtain ⟨_, h5, h6, _⟩ := linkB_iff.1 h3
  refine mem_tch.2 ⟨h1, ?_⟩
  rcases le_total a b with hab | hab
  · rwa [min_eq_left hab] at h5
  · rwa [max_eq_left hab] at h6
end PaddedDescent.F.Mark.Val
