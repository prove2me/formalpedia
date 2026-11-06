-- Prove2me | solution 1 for VariableBound.Net.SizeP.card_var_at_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:48:01.6256+00:00
-- url     : https://prove2.me/submissions/931d2f90-a863-4491-9487-98aeb36e38d0

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
import Theorems.Thm_VariableBound_Net_SizeP_card_clauses_at_le
import Theorems.Thm_VariableBound_Net_SizeP_card_objs_of_clause_le
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Net_Basic_cl_lt
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
    #((range (objs D).length).filter fun o => ∃ l ∈ clOf D o, l.1 / qv g n = a) ≤ qv g n * Δ * (1 + c) := by
  have h := card_le_mul_card_image_of_maps_to (s := (range (objs D).length).filter fun o => ∃ l ∈ clOf D o, l.1 / qv g n = a)
    (t := (range D.1.length).filter fun e => ∃ l ∈ D.1.getD e [], l.1 / qv g n = a) (f := fun o => (obAt D o).2.1) ?_ (1 + c) ?_
  · calc _ ≤ (1 + c) * _ := h
      _ ≤ (1 + c) * (qv g n * Δ) := Nat.mul_le_mul_left _ (card_clauses_at_le hg hW hΔ a)
      _ = qv g n * Δ * (1 + c) := Nat.mul_comm _ _
  · intro o ho
    obtain ⟨ho1, ho2⟩ := mem_filter.1 ho
    exact mem_filter.2 ⟨mem_range.2 (Basic.cl_lt hW (mem_range.1 ho1)), ho2⟩
  · intro e he
    have h1 := hc e (mem_range.1 (mem_filter.1 he).1)
    refine (card_le_card ?_).trans ((card_objs_of_clause_le hW e).trans (by omega))
    intro o ho
    obtain ⟨ho1, ho2⟩ := mem_filter.1 ho
    exact mem_filter.2 ⟨(mem_filter.1 ho1).1, ho2⟩
end VariableBound.Net.SizeP
