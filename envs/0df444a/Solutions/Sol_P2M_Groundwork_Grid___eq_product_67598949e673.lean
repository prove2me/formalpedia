-- Prove2me | solution 1 for P2M_Groundwork_Grid___eq_product_67598949e673
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:36:14.794178+00:00
-- url     : https://prove2.me/submissions/5262aeba-bf8a-43ba-8eb4-d2089e6238c1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Defs
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Groundwork_Grid_Grid

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution : Ω ρ γ = pairs ρ ×ˢ (univ.filter fun k : γ × γ => k.1 < k.2) := by
  ext ω; simp [Ω, pairs]
end Groundwork.Grid
