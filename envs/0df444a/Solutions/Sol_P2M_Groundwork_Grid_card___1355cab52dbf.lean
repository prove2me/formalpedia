-- Prove2me | solution 1 for P2M_Groundwork_Grid_card___1355cab52dbf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:06:30.550362+00:00
-- url     : https://prove2.me/submissions/1eec6b8b-8dcd-4c6a-ba14-ae38ea4a313f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Defs
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Groundwork_Grid_Grid
import Theorems.Thm_P2M_Groundwork_Grid___eq_product_67598949e673
import Theorems.Thm_Groundwork_card_pairs


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution {g : ℕ} (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g) : #(Ω ρ γ) = g.choose 2 ^ 2 := by
  rw [Ω_eq_product, Finset.card_product]
  change #(pairs ρ) * #(pairs γ) = _
  rw [card_pairs, card_pairs, hρ, hγ, sq]
end Groundwork.Grid
