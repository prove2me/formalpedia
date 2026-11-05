-- Prove2me | solution 1 for P2M_Groundwork_Grid_prod___rows_436f8d628931
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:40:02.604022+00:00
-- url     : https://prove2.me/submissions/3418eb32-06ba-440e-84bc-d0f13ed0efb5

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

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution {M : Type} [CommMonoid M] (F : Rect ρ γ → M) :
    ∏ ω ∈ Ω ρ γ, F ω = ∏ p ∈ pairs ρ, ∏ k : γ × γ with k.1 < k.2, F (p, k) := by
  rw [Ω_eq_product, Finset.prod_product]
end Groundwork.Grid
