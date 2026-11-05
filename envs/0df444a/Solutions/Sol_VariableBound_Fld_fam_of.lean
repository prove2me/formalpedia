-- Prove2me | solution 1 for VariableBound.Fld.fam_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:53:13.964033+00:00
-- url     : https://prove2.me/submissions/5a8a6fff-d369-4e67-8f17-7053f4945b55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Search
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Field_Family
import Theorems.Thm_VariableBound_Fld_decQ_inj
import Theorems.Thm_VariableBound_Fld_decQ_surj
import Theorems.Thm_VariableBound_Fld_setD_gamW
import Theorems.Thm_VariableBound_Fld_length_gamW
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
import Theorems.Thm_VariableBound_Fld_gamW_lt
import Theorems.Thm_VariableBound_Fld_gamW_nodup
import Theorems.Thm_VariableBound_Fld_gamW_sorted
import Theorems.Thm_VariableBound_Fld_isFamily_list
import Theorems.Thm_VariableBound_Fld_nodup_quad
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
open VariableBound VariableBound.Fld
open Groundwork Finset Polynomial
attribute [local instance] fintypeFW
namespace VariableBound.Fld
theorem _root_.solution (h14 : AppVariables.LemFamily) (m a : ℕ) (g : List Bool) (ha : 1 ≤ a) (hm : 2 ^ a ≤ m) (hs1 : 16 * m ≤ 2 ^ g.length) (hs2 : 2 ^ g.length < 32 * m)
    (hirr : Irreducible (modP g)) (Lst : List (List ℕ))
    (hLst : Lst = ((wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length).filter fun u =>
      decide (2 ^ a * (gamW m a g u).length ≤ 16 * m)).map (gamW m a g)) :
    Lst ≠ [] ∧ Lst.length < (32 * m) ^ 4 ∧ (∀ l ∈ Lst, l.Pairwise (· < ·) ∧ l.Nodup ∧ ∀ E ∈ l, E < m) ∧
    AppVariables.IsFamily (2 ^ a) (Finset.univ : Finset (Fin Lst.length)) fun i => setD m (Lst.get i) := by
  subst hLst
  have : Fact (Irreducible (modP g)) := ⟨hirr⟩
  have hm1 : 1 ≤ m := Nat.one_le_two_pow.trans hm
  have hg : 1 ≤ g.length := by
    by_contra h
    have h0 : g.length = 0 := by omega
    rw [h0] at hs1
    omega
  have hm2 : m ≤ 2 ^ g.length := by omega
  obtain ⟨hpos, hcard, hfam⟩ := h14 (FW g) m g.length a (bitsW g) (thetaW g m hm2) ha hm hs1 hs2
  have key := isFamily_list (AppVariables.Om (bitsW g) (thetaW g m hm2) a) (AppVariables.Gam (bitsW g) (thetaW g m hm2) a)
    ((wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length).filter fun u => decide (2 ^ a * (gamW m a g u).length ≤ 16 * m))
    (decQ g) (gamW m a g) ((nodup_quad g.length).filter _)
    (fun u hu u' hu' h => decQ_inj g (List.mem_of_mem_filter hu) (List.mem_of_mem_filter hu') h)
    (fun w => by
      simp only [AppVariables.Om, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_filter, decide_eq_true_eq]
      constructor
      · intro hw
        obtain ⟨u, hu, rfl⟩ := decQ_surj g w
        exact ⟨u, ⟨hu, by rw [length_gamW g hg m a hm2 hu]; exact hw⟩, rfl⟩
      · rintro ⟨u, ⟨hu, hw⟩, rfl⟩
        rw [← length_gamW g hg m a hm2 hu]; exact hw)
    (fun u hu => setD_gamW g hg m a hm2 (List.mem_of_mem_filter hu)) hfam
  refine ⟨?_, by rw [← key.1]; exact hcard, fun l hl => ?_, key.2⟩
  · refine List.ne_nil_of_length_pos ?_
    rw [← key.1]
    exact hpos
  · obtain ⟨u, _, rfl⟩ := List.mem_map.1 hl
    exact ⟨gamW_sorted m a g u, gamW_nodup m a g u, gamW_lt m a g u⟩
end VariableBound.Fld
