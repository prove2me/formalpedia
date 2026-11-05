-- Prove2me | solution 1 for Sat3.add_two_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:32:48.373195+00:00
-- url     : https://prove2.me/submissions/ea6b7b34-3069-48d2-97d8-c6e6b67482e6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas

set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
theorem _root_.solution (m : ℕ) : m + 2 ≤ 2 ^ (Nat.log2 m + 2) := by
  have h1 : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  have h2 : 2 ^ 1 ≤ 2 ^ (Nat.log2 m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (Nat.log2 m + 2) = 2 * 2 ^ (Nat.log2 m + 1) := by ring
  omega
end Sat3
