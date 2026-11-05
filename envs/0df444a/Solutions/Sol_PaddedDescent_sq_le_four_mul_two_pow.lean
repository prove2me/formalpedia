-- Prove2me | solution 1 for PaddedDescent.sq_le_four_mul_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:34:41.190524+00:00
-- url     : https://prove2.me/submissions/75985249-68d3-42ed-ae51-f3f517fdc644

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_PaddedDescent_PadRate

set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
namespace PaddedDescent
theorem _root_.solution (L : ℕ) : L * L ≤ 4 * 2 ^ L := by
  have h1 : L / 2 < 2 ^ (L / 2) := Nat.lt_two_pow_self
  have h2 : L ≤ 2 * 2 ^ (L / 2) := by omega
  calc L * L ≤ (2 * 2 ^ (L / 2)) * (2 * 2 ^ (L / 2)) := Nat.mul_le_mul h2 h2
    _ = 4 * 2 ^ (L / 2 + L / 2) := by rw [pow_add]; ring
    _ ≤ 4 * 2 ^ L := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
end PaddedDescent
