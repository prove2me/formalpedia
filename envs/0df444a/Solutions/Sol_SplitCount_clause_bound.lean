-- Prove2me | solution 1 for SplitCount.clause_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:28:23.110794+00:00
-- url     : https://prove2.me/submissions/ec066adb-357e-4f12-b616-3545c3668e7e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Width
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_SplitCount_Leaf

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight.Width Occ
namespace SplitCount
theorem _root_.solution {w n M : ℕ} (hn : n ≤ M) (h1 : 1 ≤ M) : w * (n + 2 + 1) + 1 + 1 ≤ (4 * w + 2) * M := by
  have a1 : w * (n + 2 + 1) ≤ w * (4 * M) := Nat.mul_le_mul_left _ (by omega)
  have a2 : (4 * w + 2) * M = w * (4 * M) + 2 * M := by ring
  omega
end SplitCount
