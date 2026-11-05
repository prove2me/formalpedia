-- Prove2me | solution 1 for WidthK.ProgMain.card_le_of_clause
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:42:38.374012+00:00
-- url     : https://prove2.me/submissions/33ca25ad-b9fe-4369-8500-98f9d8047a69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open WidthK WidthK.ProgMain
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}
namespace WidthK.ProgMain
theorem _root_.solution {F₀ F : Finset (Finset PLit)} (hk : ∀ C ∈ F₀, C.card ≤ k) (h : ∀ C ∈ F, ∃ C₀ ∈ F₀, C ⊆ C₀) :
    F.card ≤ F₀.card * 2 ^ k := by
  have hsub : F ⊆ F₀.biUnion Finset.powerset := by
    intro C hC
    obtain ⟨C₀, hC₀, hs⟩ := h C hC
    exact mem_biUnion.2 ⟨C₀, hC₀, mem_powerset.2 hs⟩
  refine (card_le_card hsub).trans (card_biUnion_le_card_mul _ _ _ fun C hC => ?_)
  rw [card_powerset]
  exact Nat.pow_le_pow_right (by norm_num) (hk C hC)
end WidthK.ProgMain
