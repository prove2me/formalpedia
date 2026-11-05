-- Prove2me | solution 1 for WidthK.SetAlg.card_petal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:17:43.236227+00:00
-- url     : https://prove2.me/submissions/e711d1dc-c8e0-449e-bf05-7f1f90b85674

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_SetAlg
import Theorems.Thm_WidthK_SetAlg_mem_over
import Theorems.Thm_WidthK_SetAlg_mem_petals

set_option autoImplicit false
section
section
open WidthK WidthK.SetAlg
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
namespace WidthK.SetAlg
theorem _root_.solution {F : Finset (Finset α)} {j : ℕ} {H D : Finset α} (hD : D ∈ petals F j H) : D.card = j - H.card := by
  obtain ⟨C, hC, rfl⟩ := mem_petals.1 hD
  obtain ⟨-, hj, hs⟩ := mem_over.1 hC
  rw [card_sdiff_of_subset hs, hj]
end WidthK.SetAlg
