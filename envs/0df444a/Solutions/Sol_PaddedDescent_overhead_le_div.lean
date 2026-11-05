-- Prove2me | solution 1 for PaddedDescent.overhead_le_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:29:53.483375+00:00
-- url     : https://prove2.me/submissions/587a9fd3-bc6c-4b5d-aeac-0703b5007920

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
import Theorems.Thm_PaddedDescent_overhead_mul_le

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution {s n W a c : ℕ} (hc : c ≤ 2 ^ 500) (hn : Ytop s ^ (2 * a + 2) ≤ n)
    (hW : W ≤ c * Ytop s ^ a * (Nat.sqrt n + 1)) : W ≤ n / 2 ^ s :=
  (Nat.le_div_iff_mul_le (by positivity)).2 (overhead_mul_le hc hn hW)
end PaddedDescent
