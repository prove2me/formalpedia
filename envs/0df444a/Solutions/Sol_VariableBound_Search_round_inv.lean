-- Prove2me | solution 1 for VariableBound.Search.round_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:38:35.991078+00:00
-- url     : https://prove2.me/submissions/0e5ccf57-106e-4ef9-9377-8b3d72815c8f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Defs
import Definitions.Def_VariableBound_StepChoice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Search_Correct
import Theorems.Thm_VariableBound_Search_chksD_append
import Theorems.Thm_VariableBound_Search_den_pos
import Theorems.Thm_VariableBound_Search_ups_eq
import Theorems.Thm_VariableBound_Search_argminD_spec
import Theorems.Thm_VariableBound_Search_structD_inv
import Theorems.Thm_VariableBound_Search_structD_more
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
import Theorems.Thm_VariableBound_StepChoice_Xsum_nonneg
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
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F AppVariables Finset
variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (n nb rb tb : ℕ) (fam : List (List ℕ))
variable {V n nb rb tb fam}
namespace VariableBound.Search
theorem _root_.solution (H : Hyp X m n nb rb tb fam) (evX : List (List ℕ) → ℤ) (hev : ∀ L, StructD m nb rb tb L → evX L = Xsum V nb (chksD m L))
    (L : List (List ℕ)) (hL : Inv V n nb rb tb fam L) :
    Inv V n nb rb tb fam (roundD evX fam m nb (beta n m nb) rb tb L) ∧
      (Xsum V nb (chksD m L) = 0 → roundD evX fam m nb (beta n m nb) rb tb L = L) ∧
      (Xsum V nb (chksD m L) ≠ 0 → (roundD evX fam m nb (beta n m nb) rb tb L).length = L.length + 1) := by
  unfold roundD
  rw [hev L (structD_inv H L hL)]
  by_cases h0 : Xsum V nb (chksD m L) = 0
  · rw [if_pos h0]; exact ⟨hL, fun _ => rfl, fun h => absurd h0 h⟩
  · rw [if_neg h0]
    have hpos : 0 < Xsum V nb (chksD m L) := lt_of_le_of_ne (StepChoice.Xsum_nonneg V nb _) (Ne.symm h0)
    obtain ⟨hmem, hmin⟩ := argminD_spec (fun l => upsNum m nb (beta n m nb) rb tb (evX (L ++ [l])) (L ++ [l])) fam H.hne
    generalize argminD (fun l => upsNum m nb (beta n m nb) rb tb (evX (L ++ [l])) (L ++ [l])) fam = a at hmem hmin
    have hups : ∀ l ∈ fam, Ups V nb (beta n m nb) rb tb (chksD m L ++ [Fld.setD m l]) =
        (upsNum m nb (beta n m nb) rb tb (evX (L ++ [l])) (L ++ [l]) : ℚ) / den nb (beta n m nb) rb tb (L.length + 1) := by
      intro l hl
      rw [hev _ (structD_more H L hL hpos l hl), ← chksD_append, ups_eq m V nb _ rb tb _ H.hnb, List.length_append, List.length_singleton]
    refine ⟨⟨?_, ?_⟩, fun h => absurd h h0, fun _ => by simp⟩
    · intro l' h'
      rcases List.mem_append.1 h' with h' | h'
      · exact hL.1 l' h'
      · rw [List.mem_singleton.1 h']; exact hmem
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hmem
      rw [chksD_append]
      refine Reached.step (Γ := fun i => Fld.setD m (fam.get i)) (chksD m L) i hL.2 hpos (mem_univ i) fun u' _ => ?_
      rw [hups _ hmem, hups _ (List.get_mem fam u')]
      refine div_le_div_of_nonneg_right ?_ (den_pos nb _ rb tb _ H.hnb).le
      exact_mod_cast hmin _ (List.get_mem fam u')
end VariableBound.Search
