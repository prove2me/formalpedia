-- Prove2me | solution 1 for P2M_Eight_p__eq_750c2ead4896
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:47:38.750328+00:00
-- url     : https://prove2.me/submissions/803d244e-5c29-4e48-80ba-ee864e6141c4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eight_SecCrossing_Identity
import Theorems.Thm_Eight_bxor_cancel_left
import Theorems.Thm_Eight_d_eq

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {p q p' q' : Block} (h : bxor p q = bxor p' q') : p' = bxor p (bxor q q') := by
  rw [d_eq h, bxor_cancel_left]
end Eight
