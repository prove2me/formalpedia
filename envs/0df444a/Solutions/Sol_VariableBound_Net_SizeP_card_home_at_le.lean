-- Prove2me | solution 1 for VariableBound.Net.SizeP.card_home_at_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:35:05.291198+00:00
-- url     : https://prove2.me/submissions/cb2d815f-f951-4922-9069-33051bc7a327

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Net_SizeB
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Net_SizeP
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Net_Basic_inc_mem
import Theorems.Thm_VariableBound_Net_Basic_obAt_inj
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}
namespace VariableBound.Net.SizeP
theorem _root_.solution (hW : WfD k n D) (a : ℕ) :
    #((range (objs D).length).filter fun o => (obAt D o).1 = 1 ∧ home g (obAt D o).2.2 = a) ≤
      ∑ j ∈ (range D.2.length).filter (fun j => home g j = a), (D.2.getD j []).length := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun o => (obAt D o).2.2) (t := (range D.2.length).filter fun j => home g j = a)]
  · refine sum_le_sum fun j _ => ?_
    refine (card_le_card_of_injOn (t := (D.2.getD j []).toFinset) (fun o => (obAt D o).2.1) ?_ ?_).trans (List.toFinset_card_le _)
    · intro o ho
      obtain ⟨ho1, ho2⟩ := mem_filter.1 (mem_coe.1 ho)
      obtain ⟨ho3, ho4⟩ := mem_filter.1 ho1
      exact mem_coe.2 (List.mem_toFinset.2 (ho2 ▸ (Basic.inc_mem (mem_range.1 ho3) ho4.1).2))
    · intro o ho o' ho' heq
      obtain ⟨ho1, ho2⟩ := mem_filter.1 (mem_coe.1 ho)
      obtain ⟨ho3, ho4⟩ := mem_filter.1 ho1
      obtain ⟨ho1', ho2'⟩ := mem_filter.1 (mem_coe.1 ho')
      obtain ⟨ho3', ho4'⟩ := mem_filter.1 ho1'
      exact Basic.obAt_inj hW (mem_range.1 ho3) (mem_range.1 ho3') (Prod.ext (ho4.1.trans ho4'.1.symm) (Prod.ext heq (ho2.trans ho2'.symm)))
  · intro o ho
    obtain ⟨ho1, ho2⟩ := mem_filter.1 (mem_coe.1 ho)
    exact mem_coe.2 (mem_filter.2 ⟨mem_range.2 (Basic.inc_mem (mem_range.1 ho1) ho2.1).1, ho2.2⟩)
end VariableBound.Net.SizeP
