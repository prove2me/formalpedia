-- Prove2me | solution 1 for StepSparsify.yC_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:47:05.244019+00:00
-- url     : https://prove2.me/submissions/c9148323-8564-4966-838c-a300768c6f8b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_CalNumbers
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Real
import Definitions.Def_SparsificationLemma_Cal_Facts
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_StepSparsify_CalLeaves
import Theorems.Thm_SparsificationLemma_Cal_stAlpha
import Theorems.Thm_SparsificationLemma_Cal_stYLe
import Theorems.Thm_SparsificationLemma_Cal_xC_cast
import Theorems.Thm_StepSparsify_eps_le_one
import Theorems.Thm_StepSparsify_eps_pos


set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Sparsify CountKSat SparsificationLemma
namespace StepSparsify
theorem _root_.solution (k s : ℕ) : Cal.yC (max k 3) (alphaS k s) ≤ 1 / 2 ^ s := by
  obtain ⟨a1, -, -, a4, -⟩ := Cal.stAlpha (max k 3) (1 / 2 ^ s) (le_max_right k 3) (eps_pos s) (eps_le_one s)
  have hx := Cal.xC_cast (max k 3) (1 / 2 ^ s)
  have he : (((1 / 2 ^ s : ℚ)) : ℝ) = 1 / 2 ^ s := by push_cast; rfl
  rw [he] at hx
  refine Cal.stYLe (max k 3) (alphaS k s) (1 / 2 ^ s) (le_trans (by norm_num) (le_max_right k 3)) (by positivity) ?_ ?_
  · rw [← hx]; exact_mod_cast a1
  · rw [← hx]; exact a4
end StepSparsify
