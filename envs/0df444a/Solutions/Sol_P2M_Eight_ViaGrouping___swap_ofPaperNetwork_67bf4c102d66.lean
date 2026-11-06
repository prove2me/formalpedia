-- Prove2me | solution 1 for P2M_Eight_ViaGrouping___swap_ofPaperNetwork_67bf4c102d66
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:38:45.481036+00:00
-- url     : https://prove2.me/submissions/ccd412da-462f-4f19-b83b-0c45290d02dc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution (N : Paper.Network (Fin g) (List Bool) (List Bool)) (a b : Fin g) (z z' : List Bool) : N.Ψ b a z' z = N.Ψ a b z z' := by
  unfold Groundwork.Network.Ψ Groundwork.Network.lab
  rw [min_comm, max_comm]
  exact Finset.sum_congr rfl fun θ _ => mul_comm _ _
end Eight.ViaGrouping
