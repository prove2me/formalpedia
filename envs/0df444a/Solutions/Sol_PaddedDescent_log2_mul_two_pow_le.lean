-- Prove2me | solution 1 for PaddedDescent.log2_mul_two_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:36:44.48416+00:00
-- url     : https://prove2.me/submissions/23e345f2-69c5-4378-996b-7e7e21d4f66a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_PaddedDescent_PadRate
import Theorems.Thm_PaddedDescent_sq_le_four_mul_two_pow

set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
namespace PaddedDescent
theorem _root_.solution {n s : ℕ} (hs : 2 ^ s ≤ Nat.log2 (n + 2)) : Nat.log2 (n + 2) * 2 ^ s ≤ 8 * (n + 2 ^ s) := by
  have h1 : 2 ^ Nat.log2 (n + 2) ≤ n + 2 := Nat.log2_self_le (by omega)
  have h2 := sq_le_four_mul_two_pow (Nat.log2 (n + 2))
  have h3 : Nat.log2 (n + 2) * 2 ^ s ≤ Nat.log2 (n + 2) * Nat.log2 (n + 2) := Nat.mul_le_mul_left _ hs
  have h4 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  omega
end PaddedDescent
