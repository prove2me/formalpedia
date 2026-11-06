-- Prove2me | solution 1 for VariableBound.Net.Tests.card_links_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:30:17.10116+00:00
-- url     : https://prove2.me/submissions/8fe68b1b-e43e-46cf-bc3f-4d2a9ecfc9d7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests
import Theorems.Thm_VariableBound_Net_Tests_linkB_iff
import Theorems.Thm_VariableBound_Net_Tests_card_links_lt
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff
import Theorems.Thm_PaddedDescent_F_Mark_Prof_linkB_iff
import Theorems.Thm_VariableBound_Net_Basic_card_touched_le
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}
namespace VariableBound.Net.Tests
theorem _root_.solution (e : ℕ) :
    #(((range g) ×ˢ (range g)).filter fun p => linkB g n D e p.1 p.2 = true) ≤ (clOf D e).length + (obAt D e).1 - 1 := by
  by_cases h : ∃ a < g, tchB g n D a e = true
  · have := card_links_lt e h
    have := Basic.card_touched_le (g := g) (n := n) (D := D) e
    omega
  · rw [card_eq_zero.2]
    · exact Nat.zero_le _
    · refine filter_eq_empty_iff.2 fun p hp hl => h ⟨p.1, mem_range.1 (mem_product.1 hp).1, (linkB_iff.1 hl).2.1⟩
end VariableBound.Net.Tests
