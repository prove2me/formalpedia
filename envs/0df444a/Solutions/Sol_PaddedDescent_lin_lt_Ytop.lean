-- Prove2me | solution 1 for PaddedDescent.lin_lt_Ytop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:17:36.510531+00:00
-- url     : https://prove2.me/submissions/5d9aeca4-894d-4fb6-98ee-e9d1458c3c5d

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
import Theorems.Thm_PaddedDescent_Ytop_lower


set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution (s : ℕ) : 52 * s + 694 < Ytop s :=
  lt_of_lt_of_le Nat.lt_two_pow_self (Ytop_lower s)
end PaddedDescent
