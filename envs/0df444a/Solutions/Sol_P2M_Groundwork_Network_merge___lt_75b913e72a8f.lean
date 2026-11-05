-- Prove2me | solution 1 for P2M_Groundwork_Network_merge___lt_75b913e72a8f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:04:27.86204+00:00
-- url     : https://prove2.me/submissions/06c7b46c-c322-4ed9-bb26-a33f1c970777

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_Groundwork_prod_factorised


set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
open Groundwork.Network
namespace Groundwork.Network
theorem _root_.solution [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ)
    {G G' : J'} (h : G < G') (z z' : J → σ) :
    (N.merge χ s₀ t₀).Ψ G G' z z' = ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.Ψ p.1 p.2 (z p.1) (z' p.2) := by
  have h2 : ∀ t : J × J → τ, ∏ q : J × J with χ q.1 = G' ∧ χ q.2 = G, N.f q.1 q.2 (z' q.1) (t q.swap) =
      ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.f p.2 p.1 (z' p.2) (t p) := fun t =>
    Finset.prod_nbij' Prod.swap Prod.swap (by intro p; simp [and_comm]) (by intro p; simp [and_comm]) (by intro p; simp)
      (by intro p; simp) (by intro p; simp)
  simp only [Ψ, lab, merge, h.le, min_eq_left, max_eq_right, h, ite_true, h.not_gt, ite_false, h2]
  rw [← prod_factorised]
end Groundwork.Network
