-- Prove2me | solution 1 for SparsificationLemma.Gen.ok_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:22:47.791712+00:00
-- url     : https://prove2.me/submissions/64cc3533-4402-4cf3-bb60-73ba46a7dc23

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSatRate_Tree
import Definitions.Def_SparsificationLemma_Iface
import Definitions.Def_SparsificationLemma_Shrink
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Gen
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_WidthK_ProgMain_mem_toFin
import Theorems.Thm_WidthK_Refine_mem_toFin
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
open PaddedDescent.F.Mark (occ)
open SparsificationLemma.Gen
variable {k τ n D : ℕ} {θ β : ℕ → ℕ} {ψ : PFml}
namespace SparsificationLemma.Gen
theorem _root_.solution (hψ : IsKCNF k n ψ) : ProgMain.Ok k n (toFin ψ) := by
  intro X hX
  obtain ⟨C, hC, rfl⟩ := ProgMain.mem_toFin.1 hX
  obtain ⟨a, b, c⟩ := hψ C hC
  refine ⟨fun l hl => ?_, (List.toFinset_nonempty_iff C).2 a, (List.toFinset_card_le C).trans b⟩
  rw [ProgMain.litsBelow, Finset.mem_product, Finset.mem_range]
  exact ⟨c l (List.mem_toFinset.1 hl), Finset.mem_univ _⟩
end SparsificationLemma.Gen
