-- Prove2me | solution 1 for QueryMachines.Tower.shapeS_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:19:14.382401+00:00
-- url     : https://prove2.me/submissions/b02775c3-8c97-4bf5-b061-7c57b68fa481

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Mathlib.Tactic.Ring
import Definitions.Def_Tower_Cost

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower
namespace QueryMachines.Tower
theorem _root_.solution (own calls qs : ℕ → ℕ) (l tc tc' tq tq' : ℕ) (h1 : tc ≤ tc') (h2 : tq ≤ tq') : shapeS own calls qs l tc tq ≤ shapeS own calls qs l tc' tq' :=
  Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ h1) _) (Nat.mul_le_mul_left _ h2)
end QueryMachines.Tower
