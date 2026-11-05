-- Prove2me | solution 1 for PaddedDescent.F.Mark.Val.clAt_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:18:18.187752+00:00
-- url     : https://prove2.me/submissions/c013a535-7650-4c62-8487-852f72bd4e97

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}
namespace PaddedDescent.F.Mark.Val
theorem _root_.solution {e : ℕ} (he : e < (cls Ls).length) : ∃ L ∈ Ls, (clAt Ls e).2 ∈ L := by
  have hm : clAt Ls e ∈ cls Ls := by
    rw [clAt, List.getD_eq_getElem _ _ he]
    exact List.getElem_mem he
  obtain ⟨i, hi, hq⟩ := List.mem_flatMap.1 hm
  obtain ⟨C, hC, hCe⟩ := List.mem_map.1 hq
  have hi := List.mem_range.1 hi
  rw [List.getD_eq_getElem _ _ hi] at hC
  exact ⟨Ls[i], List.getElem_mem hi, by rw [← hCe]; exact hC⟩
end PaddedDescent.F.Mark.Val
