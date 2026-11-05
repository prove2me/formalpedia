-- Prove2me | solution 1 for P2M_Eight_q__eq_27d0ba6cca4c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:46:48.959212+00:00
-- url     : https://prove2.me/submissions/591ce181-d81d-4f23-a4c6-bd4f1300f9df

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

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution (q q' : Block) : q' = bxor q (bxor q q') := (bxor_cancel_left q q').symm
end Eight
