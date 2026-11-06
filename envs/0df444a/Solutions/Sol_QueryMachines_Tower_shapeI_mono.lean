-- Prove2me | solution 1 for QueryMachines.Tower.shapeI_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:19:25.571426+00:00
-- url     : https://prove2.me/submissions/1781721d-53e0-4eab-bdf7-6c075cdceaf2

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
theorem _root_.solution (own' q' : ℕ → ℕ) (l t t' : ℕ) (h : t ≤ t') : shapeI own' q' l t ≤ shapeI own' q' l t' := Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _
end QueryMachines.Tower
