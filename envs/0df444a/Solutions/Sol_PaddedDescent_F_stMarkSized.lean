-- Prove2me | solution 1 for PaddedDescent.F.stMarkSized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:21:57.383225+00:00
-- url     : https://prove2.me/submissions/2707afc0-35f3-4a7f-9305-cdb1417cd866

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_PaddedDescent_F_Mark_Size_sized_markN
import Theorems.Thm_PaddedDescent_F_Mark_Size_U_markN_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_Mark_Deg_length_tch_le_of_wfL
import Theorems.Thm_Sat3_Is3CNF_length_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F
open Mark Mark.Size Finset
namespace PaddedDescent.F
theorem _root_.solution : StMarkSized := fun k gu nu βu bu w Δ Ls y hg h0 _ hwf hΔ hM hadm => by
  have htch := Deg.length_tch_le_of_wfL hg hwf hΔ
  refine ⟨sized_markN h0 hadm fun a _ => ?_, ?_⟩
  · have h1 := htch a
    have h2 : qv gu.length nu.length * Δ ≤ qv gu.length nu.length * (Δ + 4) := Nat.mul_le_mul_left _ (by omega)
    constructor
    · calc qv gu.length nu.length + (tch gu.length nu.length Ls a).length
          ≤ qv gu.length nu.length + qv gu.length nu.length * Δ := Nat.add_le_add_left h1 _
        _ ≤ 1 * (qv gu.length nu.length * (Δ + 4)) := by rw [Nat.one_mul, Nat.mul_add]; omega
        _ ≤ 2 * (2 + βu.length) * (qv gu.length nu.length * (Δ + 4)) := Nat.mul_le_mul_right _ (by omega)
        _ = Pb gu.length nu.length βu.length Δ := by rw [Pb]; ring
    · calc 2 * (2 + βu.length) * (tch gu.length nu.length Ls a).length
          ≤ 2 * (2 + βu.length) * (qv gu.length nu.length * (Δ + 4)) := Nat.mul_le_mul_left _ (h1.trans h2)
        _ = Pb gu.length nu.length βu.length Δ := by rw [Pb]; ring
  · refine (U_markN_le hadm fun L hL C hC => (hwf L hL C hC).2.1).trans ?_
    have hterm : ∀ i ∈ range Ls.length, (k - 1) * w * (1 + βu.length) + ((k - 1) * (Ls.getD i []).length / bu.length + gu.length * gu.length) ≤
        (k - 1) * w * (1 + βu.length) + (k - 1) * (nu.length + 1) + gu.length ^ 2 := by
      intro i hi
      have hi' := mem_range.1 hi
      have hlen : (Ls.getD i []).length ≤ Ls.flatten.length := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
        exact (List.sublist_flatten_of_mem (List.getElem_mem hi')).length_le
      have hdiv : (k - 1) * (Ls.getD i []).length / bu.length ≤ (k - 1) * (nu.length + 1) := by
        refine Nat.div_le_of_le_mul ?_
        calc (k - 1) * (Ls.getD i []).length ≤ (k - 1) * (bu.length * (nu.length + 1)) := Nat.mul_le_mul_left (k - 1) (hlen.trans hM)
          _ = bu.length * ((k - 1) * (nu.length + 1)) := by ring
      rw [sq]
      omega
    calc 2 * ∑ i ∈ range Ls.length, ((k - 1) * w * (1 + βu.length) + ((k - 1) * (Ls.getD i []).length / bu.length + gu.length * gu.length))
        ≤ 2 * ∑ _i ∈ range Ls.length, ((k - 1) * w * (1 + βu.length) + (k - 1) * (nu.length + 1) + gu.length ^ 2) :=
          Nat.mul_le_mul_left 2 (sum_le_sum hterm)
      _ = Ub k gu.length nu.length w βu.length Ls.length := by rw [sum_const, card_range, smul_eq_mul, Ub]; ring
end PaddedDescent.F
