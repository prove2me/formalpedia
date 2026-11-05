-- Prove2me | solution 1 for PaddedDescent.F.Mark.Prof.adm_match_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:29:27.941515+00:00
-- url     : https://prove2.me/submissions/3c8b6b89-a5d2-4bf7-bfb8-95f70cc4c385

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Digits
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_PaddedDescent_F_MarkProf
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mu_comm
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mu_of_le
import Theorems.Thm_PaddedDescent_F_Mark_Prof_pw_comm
import Theorems.Thm_PaddedDescent_F_Mark_Prof_sum_oc
import Theorems.Thm_PaddedDescent_F_Mark_Prof_sum_pw_le
import Theorems.Thm_PaddedDescent_F_Mark_Prof_pw_le_length
import Theorems.Thm_PaddedDescent_F_Mark_Prof_adm_iff
import Theorems.Thm_PaddedDescent_F_Mark_Prof_tgt_place
import Theorems.Thm_Groundwork_Grid_mixed_lt
import Theorems.Thm_Groundwork_Grid_mixed_surj
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_TM_beq_LR
import Theorems.Thm_Groundwork_TM_beq_RL
import Theorems.Thm_Groundwork_TM_beq_bL
import Theorems.Thm_Groundwork_TM_beq_bR
import Theorems.Thm_Groundwork_TM_length_mirror
import Theorems.Thm_Groundwork_TM_st4_cnt
import Theorems.Thm_Groundwork_TM_st4_src
import Theorems.Thm_Groundwork_TM_st4_t1
import Theorems.Thm_Groundwork_TM_st4_t2
import Theorems.Thm_Groundwork_TM_st_a
import Theorems.Thm_Groundwork_TM_st_b
import Theorems.Thm_Groundwork_TM_st_cnt
import Theorems.Thm_Groundwork_TM_st_main
import Theorems.Thm_Groundwork_TM_upd4_cnt
import Theorems.Thm_Groundwork_TM_upd4_src
import Theorems.Thm_Groundwork_TM_upd4_t1
import Theorems.Thm_Groundwork_TM_upd4_t2
import Theorems.Thm_Groundwork_TM_upd_a
import Theorems.Thm_Groundwork_TM_upd_b
import Theorems.Thm_Groundwork_TM_upd_main
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.TM.beq_LR
attribute [local simp] Groundwork.TM.beq_RL
attribute [local simp] Groundwork.TM.beq_bL
attribute [local simp] Groundwork.TM.beq_bR
attribute [local simp] Groundwork.TM.length_mirror
attribute [local simp] Groundwork.TM.st4_cnt
attribute [local simp] Groundwork.TM.st4_src
attribute [local simp] Groundwork.TM.st4_t1
attribute [local simp] Groundwork.TM.st4_t2
attribute [local simp] Groundwork.TM.st_a
attribute [local simp] Groundwork.TM.st_b
attribute [local simp] Groundwork.TM.st_cnt
attribute [local simp] Groundwork.TM.st_main
attribute [local simp] Groundwork.TM.upd4_cnt
attribute [local simp] Groundwork.TM.upd4_src
attribute [local simp] Groundwork.TM.upd4_t1
attribute [local simp] Groundwork.TM.upd4_t2
attribute [local simp] Groundwork.TM.upd_a
attribute [local simp] Groundwork.TM.upd_b
attribute [local simp] Groundwork.TM.upd_main
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.Mark.Prof
theorem _root_.solution {k g n : ℕ} (w : ℕ) {Ls : List Fml} (hg : 0 < g) (h : WfL k n Ls) {P : Finset ℕ} (hP : P ⊆ range (cls Ls).length)
    (y : ℕ) : (adm k g n w Ls y = true ∧ Match g n Ls y P) ↔
      ((∀ i < Ls.length, (layP Ls P i).card ≤ w) ∧ ∀ q < g * g * Ls.length, digit (cls Ls).length y q = tgt g n Ls P q) := by
  rw [adm_iff]
  constructor
  · rintro ⟨hadm, hM⟩
    refine ⟨fun i hi => ?_, fun q hq => ?_⟩
    · rw [← sum_oc hg h hP i, sum_congr rfl fun a ha => (hM i hi a (mem_range.1 ha)).1]
      exact (hadm i hi).1
    · obtain ⟨x, hx, i, hi, rfl⟩ := mixed_surj hq
      obtain ⟨A, hA, A', hA', rfl⟩ := mixed_surj hx
      rw [tgt_place P hA' hi]
      split_ifs with c1 c2
      · exact ((hadm i hi).2.2 A hA A' hA').1 c1
      · subst c2
        rw [(hM i hi A hA).1, mu_of_le g Ls y le_rfl]
      · have hlt : A < A' := by omega
        rw [(hM i hi A hA).2 A' hA' (by omega), mu_of_le g Ls y hlt.le]
  · rintro ⟨hc, hD⟩
    have dig : ∀ A < g, ∀ A' < g, ∀ i < Ls.length, digit (cls Ls).length y ((A * g + A') * Ls.length + i) =
        if A' < A then 0 else if A = A' then oc g n Ls P A i else pw g n Ls P A A' i := fun A hA A' hA' i hi => by
      rw [hD _ (mixed_lt (mixed_lt hA hA') hi), tgt_place P hA' hi]
    have hM : Match g n Ls y P := by
      intro i hi a ha
      refine ⟨?_, fun b hb hne => ?_⟩
      · rw [mu_of_le g Ls y le_rfl, dig a ha a ha i hi]; simp
      · rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · rw [mu_comm, mu_of_le g Ls y hlt.le, dig b hb a ha i hi, if_neg (by omega), if_neg (by omega), pw_comm]
        · rw [mu_of_le g Ls y hlt.le, dig a ha b hb i hi, if_neg (by omega), if_neg (by omega)]
    refine ⟨fun i hi => ⟨?_, ?_, fun a ha a' ha' => ⟨fun hlt => ?_, fun hlt => ?_⟩⟩, hM⟩
    · rw [← sum_congr rfl fun a ha => (hM i hi a (mem_range.1 ha)).1, sum_oc hg h hP i]
      exact hc i hi
    · rw [← sum_congr rfl fun a ha => sum_congr rfl fun a' ha' =>
        (hM i hi a' ((mem_range.1 ha').trans (mem_range.1 ha))).2 a (mem_range.1 ha) (by have := mem_range.1 ha'; omega)]
      exact (sum_pw_le hg h hP i).trans (Nat.mul_le_mul_left (k - 1) (hc i hi))
    · rw [dig a ha a' ha' i hi, if_pos hlt]
    · rw [← (hM i hi a ha).2 a' ha' (by omega)]
      exact pw_le_length _ _ _ _ _ _ _
end PaddedDescent.F.Mark.Prof
