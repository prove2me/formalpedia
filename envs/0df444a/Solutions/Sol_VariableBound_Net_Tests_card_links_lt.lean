-- Prove2me | solution 1 for VariableBound.Net.Tests.card_links_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:55:13.971662+00:00
-- url     : https://prove2.me/submissions/5ffbbc90-6cc9-41d4-9921-9d7e86995f5a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests
import Theorems.Thm_VariableBound_Net_Tests_linkB_iff
import Theorems.Thm_VariableBound_Net_Tests_link_left_unique
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff
import Theorems.Thm_PaddedDescent_F_Mark_Prof_linkB_iff
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}
namespace VariableBound.Net.Tests
theorem _root_.solution (e : ℕ) (h : ∃ a < g, tchB g n D a e = true) :
    #(((range g) ×ˢ (range g)).filter fun p => linkB g n D e p.1 p.2 = true) < #((range g).filter fun a => tchB g n D a e = true) := by
  classical
  -- the least touched node is the upper end of no link
  obtain ⟨a₀, ha₀, hmin⟩ : ∃ a₀ ∈ (range g).filter (fun a => tchB g n D a e = true),
      ∀ a ∈ (range g).filter (fun a => tchB g n D a e = true), a₀ ≤ a := by
    obtain ⟨a, ha, ht⟩ := h
    exact exists_min_image _ id ⟨a, mem_filter.2 ⟨mem_range.2 ha, ht⟩⟩
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2) (((range g) ×ˢ (range g)).filter fun p => linkB g n D e p.1 p.2 = true : Finset (ℕ × ℕ)) := by
    rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' (hbb : b = b')
    subst hbb
    have h1 := mem_filter.1 (mem_coe.1 hp)
    have h2 := mem_filter.1 (mem_coe.1 hp')
    have hb : b < g := mem_range.1 (mem_product.1 h1.1).2
    have haa : a = a' := link_left_unique hb.le h1.2 h2.2
    rw [haa]
  rw [← card_image_of_injOn hinj]
  refine card_lt_card ⟨?_, fun hsub => ?_⟩
  · intro b hb
    obtain ⟨⟨a, b'⟩, hp, rfl⟩ := mem_image.1 hb
    have h1 := mem_filter.1 hp
    exact mem_filter.2 ⟨(mem_product.1 h1.1).2, (linkB_iff.1 h1.2).2.2.1⟩
  · obtain ⟨⟨a, b⟩, hp, (hb : b = a₀)⟩ := mem_image.1 (hsub ha₀)
    subst hb
    have h1 := mem_filter.1 hp
    obtain ⟨hab, hta, -, -⟩ := linkB_iff.1 h1.2
    have := hmin a (mem_filter.2 ⟨(mem_product.1 h1.1).1, hta⟩)
    omega
end VariableBound.Net.Tests
