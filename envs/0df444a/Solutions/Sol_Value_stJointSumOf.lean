-- Prove2me | solution 1 for Value.stJointSumOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:49:16.727898+00:00
-- url     : https://prove2.me/submissions/623fa09c-c95c-41b1-a7b3-11d02a96f6fe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Blocks
import Definitions.Def_Value_Sums
import Definitions.Def_Value_Joint
import Theorems.Thm_Value_display_eq
import Theorems.Thm_Value_prod_groupTerm
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_Stepped_Runs_unique
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
namespace Value
theorem _root_.solution : StJointSumOf := by
  intro hSB hAZ hBl hSI C _ g K hK0 Np c N P B τ S h x L hL
  classical
  obtain ⟨hB1, hB2⟩ := hBl C g K hK0 Np c N P B τ S h x L hL
  calc ∑ Λ ∈ edgeStrings K L, ∏ γ, display Np c N hK0 x γ (star Λ γ)
      = ∑ Λ ∈ (edgeStrings K L).filter (AppendedZero g Np c x), ∏ γ, display Np c N hK0 x γ (star Λ γ) :=
        (Finset.sum_filter_of_ne fun Λ _ hne => by_contra fun hn => hne (hAZ C g K Np c N hK0 x Λ hn)).symm
    _ = ∑ θ ∈ blockStrings N (Paper.grouping hK0 x), ∏ γ, ∑ z ∈ tuples (fun a => Paper.grouping hK0 x a = γ) N.S [], groupTerm N (Paper.grouping hK0 x) θ γ z := by
        refine Finset.sum_nbij (readBlocks Np c hK0 x) ?_ ?_ ?_ ?_
        · intro Λ hΛ
          exact hB1 Λ (mem_filter.1 hΛ).1 (mem_filter.1 hΛ).2
        · intro Λ₁ h₁ Λ₂ h₂ e
          have h₁' := mem_filter.1 (mem_coe.1 h₁)
          have h₂' := mem_filter.1 (mem_coe.1 h₂)
          exact (hB2 _ (hB1 Λ₂ h₂'.1 h₂'.2)).unique ⟨h₁'.1, h₁'.2, e⟩ ⟨h₂'.1, h₂'.2, rfl⟩
        · intro θ hθ
          obtain ⟨Λ, ⟨h1, h2, h3⟩, _⟩ := hB2 θ (mem_coe.1 hθ)
          exact ⟨Λ, mem_coe.2 (mem_filter.2 ⟨h1, h2⟩), h3⟩
        · intro Λ hΛ
          exact prod_congr rfl fun γ _ => display_eq hSB Np c N hK0 x (mem_filter.1 hΛ).2 γ
    _ = ∑ θ ∈ blockStrings N (Paper.grouping hK0 x), ∑ z ∈ Fintype.piFinset N.S, ∏ γ, groupTerm N (Paper.grouping hK0 x) θ γ fun a => if Paper.grouping hK0 x a = γ then z a else [] :=
        sum_congr rfl fun θ _ => hSI g K (Paper.grouping hK0 x) N.S (groupTerm N (Paper.grouping hK0 x) θ)
    _ = ∑ z ∈ Fintype.piFinset N.S, ∑ θ ∈ blockStrings N (Paper.grouping hK0 x), jointTerm N (Paper.grouping hK0 x) z θ := by
        rw [sum_comm]
        exact sum_congr rfl fun z _ => sum_congr rfl fun θ _ => prod_groupTerm N (Paper.grouping hK0 x) z θ
end Value
