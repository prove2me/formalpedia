-- Prove2me | solution 1 for VariableBound.Net.SizeP.length_tch_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:00:18.153629+00:00
-- url     : https://prove2.me/submissions/5d884807-95d1-4b3b-9558-2a1112c6c12a

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
import Theorems.Thm_VariableBound_Net_SizeP_card_var_at_le
import Theorems.Thm_VariableBound_Net_SizeP_card_home_at_le
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Net_Basic_tchB_iff
import Theorems.Thm_VariableBound_Net_SizeB_length_filter_eq_card
import Theorems.Thm_VariableBound_Net_Tests_length_filter_eq_card
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
theorem _root_.solution (hg : 0 < g) (hW : WfD k n D) (hΔ : ∀ v, (occ D.1 v).length ≤ Δ) {c : ℕ} (hc : ∀ e < D.1.length, colD D e ≤ c) (a : ℕ) :
    (tch g n D a).length ≤ qv g n * Δ * (1 + c) + ∑ j ∈ (range D.2.length).filter (fun j => home g j = a), (D.2.getD j []).length := by
  classical
  rw [tch, Tests.length_filter_eq_card]
  refine (card_le_card (t := ((range (objs D).length).filter fun o => ∃ l ∈ clOf D o, l.1 / qv g n = a) ∪
    ((range (objs D).length).filter fun o => (obAt D o).1 = 1 ∧ home g (obAt D o).2.2 = a)) ?_).trans
    ((card_union_le _ _).trans (Nat.add_le_add (card_var_at_le hg hW hΔ hc a) (card_home_at_le hW a)))
  intro o ho
  obtain ⟨ho1, ho2⟩ := mem_filter.1 ho
  rcases Basic.tchB_iff.1 ho2 with h | h
  · exact mem_union_left _ (mem_filter.2 ⟨ho1, h⟩)
  · exact mem_union_right _ (mem_filter.2 ⟨ho1, h⟩)
end VariableBound.Net.SizeP
