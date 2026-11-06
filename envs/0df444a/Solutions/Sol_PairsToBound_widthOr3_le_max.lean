-- Prove2me | solution 1 for PairsToBound.widthOr3_le_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:02:03.160524+00:00
-- url     : https://prove2.me/submissions/667c82ca-124d-4ebe-9c9f-0d4bb6393e29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Width
import Theorems.Thm_PairsToBound_foldr_max_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_NetE_foldr_max_le
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PairsToBound
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution {n k : ℕ} {φ : CNF n} (h : ∀ C ∈ φ, C.length ≤ k) : widthOr3 φ ≤ max k 3 := by
  refine foldr_max_le (le_max_right _ _) fun x hx => ?_
  obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hx
  exact (h C hC).trans (le_max_left _ _)
end PairsToBound
