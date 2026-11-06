-- Prove2me | solution 1 for SparsificationLemma.stIfaceC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:08:00.791977+00:00
-- url     : https://prove2.me/submissions/daad5c05-ce09-4820-9e94-eb00e6c9b3bd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_SparsificationLemma_Bound
import Definitions.Def_UniformInK_Spars_Step
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsificationLemma_Iface
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Bound_bound
import Theorems.Thm_SparsificationLemma_stBoundC
import Theorems.Thm_UniformInK_Bound_bound
import Theorems.Thm_UniformInK_stNodeRootU
import Theorems.Thm_UniformInK_stNodeStepU
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
open SparsificationLemma
open Finset Groundwork Groundwork.Sparsify WidthK WidthK.Prog WidthK.ProgMain UniformInK
namespace SparsificationLemma
theorem _root_.solution : StIfaceC := fun k τ n D θ β hT hD =>
  { root := fun F₀ h => ⟨h, stNodeRootU _ _ _ _ _⟩
    step := fun F₀ F p t j H hN hR => by
      obtain ⟨a, b⟩ := stNodeStepU _ _ _ _ _ _ _ _ _ _ hT.pos hN.2 hR
      exact ⟨⟨hN.1, a⟩, ⟨hN.1, b⟩⟩
    bound := fun F₀ F p t hN => by
      obtain ⟨a, b⟩ := stBoundC _ θ β k τ n F₀ F (litsBelow n) p t hT (card_litsBelow n) (fun C hC => (hN.1 C hC).1) hN.2
      exact ⟨a.trans hD, b⟩
    clause := fun F₀ F p t hN C hC => by
      obtain ⟨C', hC', hs, -⟩ := hN.2.1 C hC
      exact ⟨C', hC', hs⟩
    leaf := fun F₀ F p t hN hL => by
      refine stLeafCard _ θ k n F (litsBelow n) hT.pos (card_litsBelow n) (fun C hC => ?_) hL
      obtain ⟨C', hC', hs, hne⟩ := hN.2.1 C hC
      obtain ⟨a, b, c⟩ := hN.1 C' hC'
      exact ⟨hs.trans a, hne b, (card_le_card hs).trans c⟩
    sat := fun F₀ F p t j H v _ _ => stSatIff _ _ _ _ _
    light_eq := fun F₀ F p t j H hN hR => by
      obtain ⟨-, N, a, h, hI, -⟩ := hN.2
      exact stLightEq _ _ _ _ _ hT.pos hI.red hR.heart
    heavy_eq := fun F₀ F p t j H hN hR => by
      obtain ⟨-, N, a, h, hI, -⟩ := hN.2
      exact stHeavyEq _ _ _ _ _ hI.red hR.heart }
end SparsificationLemma
