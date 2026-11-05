-- Prove2me | solution 1 for PaddedDescent.sOf_mul_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:33:20.528289+00:00
-- url     : https://prove2.me/submissions/ddb1efcb-cd59-41c5-ab93-8b00105ff19f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_Threshold

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution {n : ℕ} (h : 1 ≤ sOf n) : depthOf (sOf n) + 211 ≤ Nat.log2 (Nat.log2 n) := by
  unfold depthOf sOf at *; omega
end PaddedDescent
