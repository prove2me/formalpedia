-- Prove2me | solution 1 for PaddedDescent.overhead_sOf_le_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:39:43.197758+00:00
-- url     : https://prove2.me/submissions/30d53f79-5ac4-40d4-bfee-4bb7a97b7eef

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
import Theorems.Thm_PaddedDescent_overhead_le_div
import Theorems.Thm_PaddedDescent_Ytop_sOf_pow_le

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution {n W a c : ℕ} (h : 1 ≤ sOf n) (ha : 2 * a + 2 ≤ 2 ^ 200) (hc : c ≤ 2 ^ 500)
    (hW : W ≤ c * Ytop (sOf n) ^ a * (Nat.sqrt n + 1)) : W ≤ n / 2 ^ sOf n :=
  overhead_le_div hc (Ytop_sOf_pow_le ha h) hW
end PaddedDescent
