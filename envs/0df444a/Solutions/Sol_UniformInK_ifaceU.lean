-- Prove2me | solution 1 for UniformInK.ifaceU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:43:13.96504+00:00
-- url     : https://prove2.me/submissions/17beb95b-b170-46ff-857e-e130b7e9aa66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_UniformInK_Spars_Iface
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_WidthK_InvK_step
import Theorems.Thm_WidthK_Node_bound
import Theorems.Thm_WidthK_ProgMain_card_litsBelow
import Theorems.Thm_WidthK_SetAlg_heavy_eq
import Theorems.Thm_WidthK_SetAlg_light_eq
import Theorems.Thm_WidthK_stHeavyEq
import Theorems.Thm_WidthK_stLeafCard
import Theorems.Thm_WidthK_stLightEq
import Theorems.Thm_WidthK_stSatIff


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK WidthK.Prog WidthK.ProgMain
namespace UniformInK
theorem _root_.solution (h1 : StNodeRootU) (h2 : StNodeStepU) (h3 : StNodeBoundU) (h8 : StThrU) (h9 : StBetaSumU) : StIfaceU := fun τ k n hk hτ =>
  { root := fun F₀ h => ⟨h, h1 _ _ _ _ _⟩
    step := fun F₀ F p t j H hN hR => by
      obtain ⟨a, b⟩ := h2 _ _ _ _ _ _ _ _ _ _ (h8 k τ hk hτ).pos hN.2 hR
      exact ⟨⟨hN.1, a⟩, ⟨hN.1, b⟩⟩
    bound := fun F₀ F p t hN => by
      obtain ⟨a, b⟩ := h3 _ (thetaU τ) (betaSU τ) k τ n F₀ F (litsBelow n) p t (h8 k τ hk hτ) (card_litsBelow n) (fun C hC => (hN.1 C hC).1) hN.2
      exact ⟨a.trans (Nat.mul_le_mul_right _ (h9 τ k (by omega))), b⟩
    clause := fun F₀ F p t hN C hC => by
      obtain ⟨C', hC', hs, -⟩ := hN.2.1 C hC
      exact ⟨C', hC', hs⟩
    leaf := fun F₀ F p t hN hL => by
      refine stLeafCard _ (thetaU τ) k n F (litsBelow n) (h8 k τ hk hτ).pos (card_litsBelow n) (fun C hC => ?_) hL
      obtain ⟨C', hC', hs, hne⟩ := hN.2.1 C hC
      obtain ⟨a, b, c⟩ := hN.1 C' hC'
      exact ⟨hs.trans a, hne b, (card_le_card hs).trans c⟩
    sat := fun F₀ F p t j H v _ _ => stSatIff _ _ _ _ _
    light_eq := fun F₀ F p t j H hN hR => by
      obtain ⟨-, N, a, h, hI, -⟩ := hN.2
      exact stLightEq _ _ _ _ _ (h8 k τ hk hτ).pos hI.red hR.heart
    heavy_eq := fun F₀ F p t j H hN hR => by
      obtain ⟨-, N, a, h, hI, -⟩ := hN.2
      exact stHeavyEq _ _ _ _ _ hI.red hR.heart }
end UniformInK
