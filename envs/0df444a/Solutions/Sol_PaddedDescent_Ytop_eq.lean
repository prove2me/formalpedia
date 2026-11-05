-- Prove2me | solution 1 for PaddedDescent.Ytop_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:17:58.159965+00:00
-- url     : https://prove2.me/submissions/9e002cb4-b016-4a3e-a664-59e322b4d91a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution (s : ℕ) : Ytop s = 9 * Ktop s ^ 16 := by
  rw [Ytop, gtop]; ring
end PaddedDescent
