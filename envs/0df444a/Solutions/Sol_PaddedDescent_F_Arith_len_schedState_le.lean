-- Prove2me | solution 1 for PaddedDescent.F.Arith.len_schedState_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:04:20.559924+00:00
-- url     : https://prove2.me/submissions/33f0b267-5817-45a5-9ec3-f2e2448e947d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithCol
import Definitions.Def_PaddedDescent_F_ArithSched
import Theorems.Thm_PaddedDescent_F_Arith_len_schedL_le
import Theorems.Thm_Groundwork_len_units


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork PaddedDescent.F.Lists
open PaddedDescent.F.Arith
namespace PaddedDescent.F.Arith
theorem _root_.solution (j : ℕ) : len (schedState j) ≤ schedLen j := by
  have := len_schedL_le j
  rw [schedState, len_pair, len_pair, len_units, len_units, List.length_replicate, List.length_replicate, schedLen]
  nlinarith
end PaddedDescent.F.Arith
