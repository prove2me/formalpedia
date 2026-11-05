-- Prove2me | solution 1 for PaddedDescent.F.Arith.four_mul_nRect_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:59:49.749644+00:00
-- url     : https://prove2.me/submissions/84ddac76-6973-4ff9-a4c6-8e4368a26bba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithLevel
import Theorems.Thm_Groundwork_GridArith_four_mul_choose_sq_le


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (g : ℕ) : 4 * Groundwork.Prog.nRect g ≤ g ^ 4 := Groundwork.GridArith.four_mul_choose_sq_le g
end PaddedDescent.F.Arith
