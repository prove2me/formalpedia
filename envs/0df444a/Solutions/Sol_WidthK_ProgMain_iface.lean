-- Prove2me | solution 1 for WidthK.ProgMain.iface
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:41:34.446265+00:00
-- url     : https://prove2.me/submissions/8fa43b1a-39eb-47a8-9849-f0005b936764

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain
import Theorems.Thm_WidthK_ProgMain_card_litsBelow
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open WidthK WidthK.ProgMain
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
namespace WidthK.ProgMain
theorem _root_.solution (h1 : StNodeRoot) (h2 : StNodeStep) (h3 : StNodeBound) (h4 : StLeafCard) (h5 : StLightEq) (h6 : StHeavyEq) (h7 : StSatIff)
    (h8 : StThr) (h9 : StBetaSum) {τ : ℕ} (hτ : 1 ≤ τ) (k n : ℕ) :
    Iface (theta τ) k (bsum τ k * n) (k * n) τ (leafC τ k * n) (Ok k n)
      (fun F₀ F p t => Ok k n F₀ ∧ Node (theta τ) k τ F₀ F p t) where
  root F₀ h := ⟨h, h1 _ _ _ _ _⟩
  step F₀ F p t j H hN hR := by
    obtain ⟨a, b⟩ := h2 _ _ _ _ _ _ _ _ _ _ (h8 τ hτ).pos hN.2 hR
    exact ⟨⟨hN.1, a⟩, ⟨hN.1, b⟩⟩
  bound F₀ F p t hN := by
    obtain ⟨a, b⟩ := h3 _ (theta τ) (beta τ) k τ n F₀ F (litsBelow n) p t (h8 τ hτ) (card_litsBelow n) (fun C hC => (hN.1 C hC).1) hN.2
    exact ⟨a.trans (Nat.mul_le_mul_right _ (h9 τ k)), b⟩
  clause F₀ F p t hN C hC := by
    obtain ⟨C', hC', hs, -⟩ := hN.2.1 C hC
    exact ⟨C', hC', hs⟩
  leaf F₀ F p t hN hL := by
    refine h4 _ (theta τ) k n F (litsBelow n) (h8 τ hτ).pos (card_litsBelow n) (fun C hC => ?_) hL
    obtain ⟨C', hC', hs, hne⟩ := hN.2.1 C hC
    obtain ⟨a, b, c⟩ := hN.1 C' hC'
    exact ⟨hs.trans a, hne b, (card_le_card hs).trans c⟩
  sat F₀ F p t j H v _ _ := h7 _ _ _ _ _
  light_eq F₀ F p t j H hN hR := by
    obtain ⟨-, N, a, h, hI, -⟩ := hN.2
    exact h5 _ _ _ _ _ (h8 τ hτ).pos hI.red hR.heart
  heavy_eq F₀ F p t j H hN hR := by
    obtain ⟨-, N, a, h, hI, -⟩ := hN.2
    exact h6 _ _ _ _ _ hI.red hR.heart
end WidthK.ProgMain
