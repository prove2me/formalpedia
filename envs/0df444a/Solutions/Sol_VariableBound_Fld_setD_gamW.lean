-- Prove2me | solution 1 for VariableBound.Fld.setD_gamW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:42:44.061969+00:00
-- url     : https://prove2.me/submissions/4b8b4528-6779-4334-988d-cbbdfedc4098

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Search
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Field_Family
import Theorems.Thm_VariableBound_Fld_all_take_iff
import Theorems.Thm_VariableBound_Fld_ipW_iff
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
import Theorems.Thm_VariableBound_Fld_bitsW_decW
import Theorems.Thm_VariableBound_Fld_decW_mulW
import Theorems.Thm_VariableBound_Fld_decW_powW
import Theorems.Thm_VariableBound_Fld_decW_xorW
import Theorems.Thm_VariableBound_Fld_length_mulW
import Theorems.Thm_VariableBound_Fld_length_powW
import Theorems.Thm_VariableBound_Fld_length_xorW
import Theorems.Thm_VariableBound_Fld_mem_quad
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
theorem _root_.solution (g : List Bool) [Fact (Irreducible (modP g))] (hg : 1 ≤ g.length) (m a : ℕ) (hm : m ≤ 2 ^ g.length)
    {u : List Bool × List Bool × List Bool × List Bool} (hu : u ∈ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length) :
    setD m (gamW m a g u) = AppVariables.Gam (bitsW g) (thetaW g m hm) a (decQ g u) := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_quad.1 hu
  ext E
  simp only [setD, gamW, AppVariables.Gam, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_filter, List.mem_range, E.isLt, Bool.and_eq_true]
  refine and_congr ?_ ?_
  · have hw : (xorW (mulW g u.1 (toWord g.length E.val)) u.2.1).length = g.length := by
      rw [length_xorW, length_mulW h1, h2, min_self]
    have hd : (decQ g u).1 * thetaW g m hm E + (decQ g u).2.1 = decW g (xorW (mulW g u.1 (toWord g.length E.val)) u.2.1) := by
      rw [decW_xorW g (by rw [length_mulW h1, h2]), decW_mulW g h1]; rfl
    rw [all_take_iff hw, hd]
    refine forall₂_congr fun i _ => ?_
    rw [bitsW_decW g _ hw]
    cases (xorW (mulW g u.1 (toWord g.length E.val)) u.2.1).getD i.val false <;> simp [bitR]
  · have hp : (decQ g u).2.2.1 ^ E.val = decW g (powW g u.2.2.1 E.val) := (decW_powW hg _ _).symm
    rw [ipW_iff (length_powW hg _ _) h4, hp]
    have e1 : (bitsW g (decW g (powW g u.2.2.1 E.val)) : Fin g.length → ZMod 2) = fun i => bitR (ZMod 2) ((powW g u.2.2.1 E.val).getD i.val false) :=
      funext fun i => bitsW_decW g _ (length_powW hg _ _) i
    have e2 : (bitsW g (decQ g u).2.2.2 : Fin g.length → ZMod 2) = fun i => bitR (ZMod 2) (u.2.2.2.getD i.val false) :=
      funext fun i => bitsW_decW g _ h4 i
    rw [e1, e2]
end VariableBound.Fld
