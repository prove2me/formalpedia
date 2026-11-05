-- Prove2me | solution 1 for PaddedDescent.F.Mark.Deg.card_filter_mem_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:44:39.624209+00:00
-- url     : https://prove2.me/submissions/ee851f93-f324-473e-91e3-a73815f69b6b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_PaddedDescent_F_MarkDeg
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Deg
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)
variable {α : Type*} [DecidableEq α] {θ : ℕ → ℕ} {k : ℕ} {F : Finset (Finset α)}
namespace PaddedDescent.F.Mark.Deg
theorem _root_.solution {G : Finset (Finset α)} (hG : ∀ C ∈ G, C.card = 1) (y : α) : (G.filter fun C => y ∈ C).card ≤ 1 := by
  rw [card_le_one]
  intro C hC D hD
  obtain ⟨hC, hyC⟩ := mem_filter.1 hC
  obtain ⟨hD, hyD⟩ := mem_filter.1 hD
  obtain ⟨c, rfl⟩ := card_eq_one.1 (hG C hC)
  obtain ⟨e, rfl⟩ := card_eq_one.1 (hG D hD)
  rw [mem_singleton] at hyC hyD
  rw [← hyC, ← hyD]
end PaddedDescent.F.Mark.Deg
