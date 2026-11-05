-- Prove2me | solution 1 for PaddedDescent.F.Mark.Size.card_links_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:22.297884+00:00
-- url     : https://prove2.me/submissions/9964c22f-13e5-459f-9131-0418e48318fd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_PaddedDescent_F_Mark_Size_linkB_iff
import Theorems.Thm_PaddedDescent_F_Mark_Size_card_touched_le
import Theorems.Thm_PaddedDescent_F_Mark_Size_card_links_lt
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}
namespace PaddedDescent.F.Mark.Size
theorem _root_.solution (e : ℕ) :
    #(((range g) ×ˢ (range g)).filter fun p => linkB g n Ls e p.1 p.2 = true) ≤ (clAt Ls e).2.length - 1 := by
  by_cases h : ∃ a < g, tchB g n Ls a e = true
  · have := card_links_lt e h
    have := card_touched_le (g := g) (n := n) (Ls := Ls) e
    omega
  · rw [card_eq_zero.2]
    · exact Nat.zero_le _
    · refine filter_eq_empty_iff.2 fun p hp hl => h ⟨p.1, mem_range.1 (mem_product.1 hp).1, (linkB_iff.1 hl).2.1⟩
end PaddedDescent.F.Mark.Size
