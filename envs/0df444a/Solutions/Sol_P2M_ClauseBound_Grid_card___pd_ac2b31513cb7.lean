-- Prove2me | solution 1 for P2M_ClauseBound_Grid_card___pd_ac2b31513cb7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:43:32.338226+00:00
-- url     : https://prove2.me/submissions/749321e1-4045-41a0-a33c-83a062a053fb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
import Theorems.Thm_Groundwork_card_pairs
import Theorems.Thm_P2M_Groundwork_Grid___eq_product_67598949e673


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]
namespace ClauseBound.Grid
theorem _root_.solution {p d : ℕ} (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d) : #(Ω ρ γ) = p.choose 2 * d.choose 2 := by
  rw [Ω_eq_product, Finset.card_product]
  change #(pairs ρ) * #(pairs γ) = _
  rw [card_pairs, card_pairs, hρ, hγ]
end ClauseBound.Grid
