-- Prove2me | solution 1 for VariableBound.Net.Prof.adm_match_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:59:52.330685+00:00
-- url     : https://prove2.me/submissions/8aa2ab65-5cb6-435d-b1dc-d32f5efdb77b

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
import Theorems.Thm_VariableBound_Net_Prof_mu_comm
import Theorems.Thm_VariableBound_Net_Prof_mu_of_le
import Theorems.Thm_VariableBound_Net_Prof_pw_comm
import Theorems.Thm_VariableBound_Net_Prof_tot_of_match
import Theorems.Thm_VariableBound_Net_Prof_mu_le_of_match
import Theorems.Thm_VariableBound_Net_Prof_totP_le_of_match
import Theorems.Thm_VariableBound_Net_Prof_adm_iff
import Theorems.Thm_VariableBound_Net_Prof_tgt_place
import Theorems.Thm_Groundwork_Grid_mixed_lt
import Theorems.Thm_Groundwork_Grid_mixed_surj
import Theorems.Thm_Groundwork_Host_upd_none
import Theorems.Thm_Groundwork_Host_withIO_none
import Theorems.Thm_Groundwork_Host_withIO_some
import Theorems.Thm_Groundwork_PolyT_length
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
import Theorems.Thm_Groundwork_TM_update_withIO
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
import Theorems.Thm_PaddedDescent_F_Mark_Prof_adm_iff
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mu_comm
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mu_of_le
import Theorems.Thm_PaddedDescent_F_Mark_Prof_pw_comm
import Theorems.Thm_PaddedDescent_F_Mark_Prof_tgt_place
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.Host.upd_none
attribute [local simp] Groundwork.Host.withIO_none
attribute [local simp] Groundwork.Host.withIO_some
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
attribute [local simp] Groundwork.TM.update_withIO
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
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
namespace VariableBound.Net.Prof
theorem _root_.solution {k g n : ℕ} (nb M : ℕ) {D : Dat} (fl : Bool) (hg : 0 < g) (h : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length)
    (y : ℕ) : (admD k g n nb M D fl y = true ∧ Match g n D y P) ↔
      (Lim nb M D fl P ∧ ∀ q < g * g * 2, digit (objs D).length y q = tgt g n D P q) := by
  rw [adm_iff]
  constructor
  · rintro ⟨hadm, hM⟩
    refine ⟨?_, fun q hq => ?_⟩
    · have h0 := hadm.1
      have h1 := hadm.2.1
      rw [tot_of_match hg h hP hM (by omega)] at h0 h1
      exact ⟨h0, h1⟩
    · obtain ⟨x, hx, κ, hκ, rfl⟩ := mixed_surj hq
      obtain ⟨a, ha, b, hb, rfl⟩ := mixed_surj hx
      rw [tgt_place P hb hκ]
      split_ifs with c1 c2
      · exact ((hadm.2.2 κ hκ).2 a ha b hb).1 c1
      · subst c2
        rw [(hM κ hκ a ha).1, mu_of_le g D y le_rfl]
      · have hlt : a < b := by omega
        rw [(hM κ hκ a ha).2 b hb (by omega), mu_of_le g D y hlt.le]
  · rintro ⟨hc, hD⟩
    have dig : ∀ a < g, ∀ b < g, ∀ κ < 2, digit (objs D).length y ((a * g + b) * 2 + κ) =
        if b < a then 0 else if a = b then oc g n D P a κ else pw g n D P a b κ := fun a ha b hb κ hκ => by
      rw [hD _ (mixed_lt (mixed_lt ha hb) hκ), tgt_place P hb hκ]
    have hM : Match g n D y P := by
      intro κ hκ a ha
      refine ⟨?_, fun b hb hne => ?_⟩
      · rw [mu_of_le g D y le_rfl, dig a ha a ha κ hκ]; simp
      · rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · rw [mu_comm, mu_of_le g D y hlt.le, dig b hb a ha κ hκ, if_neg (by omega), if_neg (by omega), pw_comm]
        · rw [mu_of_le g D y hlt.le, dig a ha b hb κ hκ, if_neg (by omega), if_neg (by omega)]
    refine ⟨⟨?_, ?_, fun κ hκ => ⟨totP_le_of_match hg h hP hM hκ, fun a ha b hb => ⟨fun hlt => ?_, fun hlt => ?_⟩⟩⟩, hM⟩
    · rw [tot_of_match hg h hP hM (by omega)]; exact hc.1
    · rw [tot_of_match hg h hP hM (by omega)]; exact hc.2
    · rw [dig a ha b hb κ hκ, if_pos hlt]
    · exact mu_le_of_match hM hκ ha hb (by omega)
end VariableBound.Net.Prof
