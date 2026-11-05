-- Prove2me | solution 1 for StepSparsify.le_alphaS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:30:21.028376+00:00
-- url     : https://prove2.me/submissions/2ef5ecb5-5b7d-421c-be4a-e804b522fe37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_UniformInK_Top_Leaves
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_StepSparsify_CalNumbers
import Theorems.Thm_StepSparsify_eps_pos
import Theorems.Thm_StepSparsify_eps_le_one
import Theorems.Thm_SparsificationLemma_Cal_stAlpha


set_option autoImplicit false
section
section
open StepSparsify
open Finset PaddedDescent UniformInK SparsificationLemma
namespace StepSparsify
theorem _root_.solution (k s : ℕ) : 2 ≤ alphaS k s ∧ max k 3 ^ 2 ≤ alphaS k s := by
  obtain ⟨-, a2, a3, -⟩ := Cal.stAlpha (max k 3) (1 / 2 ^ s) (le_max_right k 3) (eps_pos s) (eps_le_one s)
  exact ⟨a2, a3⟩
end StepSparsify
