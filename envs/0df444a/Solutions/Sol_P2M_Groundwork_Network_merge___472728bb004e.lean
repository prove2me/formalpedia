-- Prove2me | solution 1 for P2M_Groundwork_Network_merge___472728bb004e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:44:24.56252+00:00
-- url     : https://prove2.me/submissions/4c160c6a-1623-4a51-b792-484bb451fc9e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_P2M_Groundwork_Network___comm_f75ed8fe8218
import Theorems.Thm_P2M_Groundwork_Network_merge___lt_75b913e72a8f

set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
open Groundwork.Network
namespace Groundwork.Network
theorem _root_.solution [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ)
    {G G' : J'} (h : G ≠ G') (z z' : J → σ) :
    (N.merge χ s₀ t₀).Ψ G G' z z' = ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.Ψ p.1 p.2 (z p.1) (z' p.2) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact merge_Ψ_lt N χ s₀ t₀ h z z'
  · rw [Ψ_comm, merge_Ψ_lt N χ s₀ t₀ h z' z]
    exact Finset.prod_nbij' Prod.swap Prod.swap (by intro p; simp [and_comm]) (by intro p; simp [and_comm])
      (by intro p; simp) (by intro p; simp) (by intro p _; simp [Ψ_comm])
end Groundwork.Network
