-- Prove2me | solution 1 for VariableBound.Net.Prof.tset_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:03:02.718132+00:00
-- url     : https://prove2.me/submissions/6ce41f59-506b-455f-9075-bba7a692e764

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_PaddedDescent_F_MarkProf
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_VariableBound_Net_Prof
import Theorems.Thm_VariableBound_Net_Prof_mem_tset
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mem_tset
import Theorems.Thm_VariableBound_Net_Basic_exists_tch
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
namespace VariableBound.Net.Prof
theorem _root_.solution {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {o : ℕ} (ho : o < (objs D).length) :
    (tset g n D o).Nonempty := by
  obtain ⟨a, ha, ht⟩ := Basic.exists_tch hg h ho
  exact ⟨a, mem_tset.2 ⟨ha, ht⟩⟩
end VariableBound.Net.Prof
