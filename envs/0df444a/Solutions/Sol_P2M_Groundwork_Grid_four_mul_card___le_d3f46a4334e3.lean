-- Prove2me | solution 1 for P2M_Groundwork_Grid_four_mul_card___le_d3f46a4334e3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:15:00.125089+00:00
-- url     : https://prove2.me/submissions/a25a94db-e827-4028-9675-af5521e09aa9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_Groundwork_Grid_Size
import Theorems.Thm_P2M_Groundwork_Grid_card___1355cab52dbf


set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]
namespace Groundwork.Grid
theorem _root_.solution {g : ℕ} (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g) : 4 * #(Ω ρ γ) ≤ g ^ 4 := by
  rw [card_Ω hρ hγ]
  have h : 2 * g.choose 2 ≤ g ^ 2 := by
    rw [Nat.choose_two_right]
    calc 2 * (g * (g - 1) / 2) ≤ g * (g - 1) := Nat.mul_div_le _ _
      _ ≤ g * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = g ^ 2 := (sq g).symm
  calc 4 * g.choose 2 ^ 2 = (2 * g.choose 2) ^ 2 := by ring
    _ ≤ (g ^ 2) ^ 2 := Nat.pow_le_pow_left h 2
    _ = g ^ 4 := by ring
end Groundwork.Grid
