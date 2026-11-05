-- Prove2me | solution 1 for PaddedDescent.F.Mark.Size.card_links_at_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:23.370964+00:00
-- url     : https://prove2.me/submissions/45e62832-e035-40cb-bb36-36e45fa021bf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_PaddedDescent_F_Mark_Size_linkB_iff
import Theorems.Thm_PaddedDescent_F_Mark_Size_link_left_unique
import Theorems.Thm_PaddedDescent_F_Mark_Size_link_right_unique
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}
namespace PaddedDescent.F.Mark.Size
theorem _root_.solution {a : ℕ} (ha : a < g) (e : ℕ) :
    #(((range g).erase a).filter fun b => linkB g n Ls e (min a b) (max a b) = true) ≤ if tchB g n Ls a e = true then 2 else 0 := by
  classical
  split_ifs with ht
  · have hsub : (((range g).erase a).filter fun b => linkB g n Ls e (min a b) (max a b) = true) ⊆
        ((range g).filter fun b => linkB g n Ls e b a = true) ∪ ((range g).filter fun b => linkB g n Ls e a b = true) := by
      intro b hb
      obtain ⟨hb1, hb2⟩ := mem_filter.1 hb
      obtain ⟨hne, hbg⟩ := mem_erase.1 hb1
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [min_eq_right hlt.le, max_eq_left hlt.le] at hb2
        exact mem_union_left _ (mem_filter.2 ⟨hbg, hb2⟩)
      · rw [min_eq_left hgt.le, max_eq_right hgt.le] at hb2
        exact mem_union_right _ (mem_filter.2 ⟨hbg, hb2⟩)
    have c1 : #((range g).filter fun b => linkB g n Ls e b a = true) ≤ 1 :=
      card_le_one.2 fun b hb b' hb' => link_left_unique ha.le (mem_filter.1 hb).2 (mem_filter.1 hb').2
    have c2 : #((range g).filter fun b => linkB g n Ls e a b = true) ≤ 1 :=
      card_le_one.2 fun b hb b' hb' => link_right_unique (mem_range.1 (mem_filter.1 hb).1) (mem_range.1 (mem_filter.1 hb').1)
        (mem_filter.1 hb).2 (mem_filter.1 hb').2
    exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))
  · refine le_of_eq (card_eq_zero.2 (filter_eq_empty_iff.2 fun b _ hl => ht ?_))
    obtain ⟨-, h2, h3, -⟩ := linkB_iff.1 hl
    rcases le_total a b with h | h
    · rwa [min_eq_left h] at h2
    · rwa [max_eq_left h] at h3
end PaddedDescent.F.Mark.Size
