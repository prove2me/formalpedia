-- Prove2me | solution 1 for StepSparsify.eps_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:58:57.869208+00:00
-- url     : https://prove2.me/submissions/45344ef1-3624-4c38-a7a6-59b8419e26a2

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

set_option autoImplicit false
section
section
open StepSparsify
open Finset PaddedDescent UniformInK SparsificationLemma
namespace StepSparsify
theorem _root_.solution (s : ℕ) : (1 : ℚ) / 2 ^ s ≤ 1 := by
  rw [div_le_one (by positivity)]
  exact one_le_pow₀ (by norm_num)
end StepSparsify
