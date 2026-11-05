-- Prove2me | solution 1 for P2M_ClauseBound_Grid_abs_rowNet___lt_05db5343e15b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:43:33.295881+00:00
-- url     : https://prove2.me/submissions/cbb17fc6-a5db-4a03-8bfb-fa715518dd74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
import Theorems.Thm_ClauseBound_Grid_abs_boole_le
import Theorems.Thm_ClauseBound_Grid_abs_mul_prod_le
import Theorems.Thm_ClauseBound_Grid_card_lt_le
import Theorems.Thm_P2M_Groundwork_Grid_rowNet___43280a58588e


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
namespace ClauseBound.Grid
theorem _root_.solution {d L b n : ℕ} (hγ : Fintype.card γ = d) (R : Inst (ρ × γ) α)
    {G : Rect ρ γ → α → α → α → α → ℤ} (C : Rect ρ γ → Cut α τ) (t₀ : τ) (hF : ∀ ω, (C ω).Factors (G ω))
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b) (hn : d ^ 2 * b ≤ n) {a c : ρ} (h : a < c) (z z' : RowSt ρ γ α) :
    |(rowNet R C t₀ L).Ψ a c z z'| ≤ 2 ^ n := by
  rw [rowNet_Ψ hF R t₀ L h]
  exact abs_mul_prod_le _ _ _ _ (fun _ => abs_boole_le _) (fun _ => hG _ _ _ _ _)
    ((Nat.mul_le_mul_right _ (card_lt_le γ hγ)).trans hn)
end ClauseBound.Grid
