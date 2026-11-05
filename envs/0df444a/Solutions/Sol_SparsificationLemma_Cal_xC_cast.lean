-- Prove2me | solution 1 for SparsificationLemma.Cal.xC_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:33:49.835358+00:00
-- url     : https://prove2.me/submissions/41c67aee-fb14-4c93-857a-ec643550c00d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Alpha

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution (k : ℕ) (ε : ℚ) : ((xC k ε : ℚ) : ℝ) = 32 * ((k : ℝ) - 1) ^ 2 / (ε : ℝ) := by
  rw [xC]; push_cast; ring
end SparsificationLemma.Cal
