-- Prove2me | solution 1 for PaddedDescent.F.Arith.nRect_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:04:39.504139+00:00
-- url     : https://prove2.me/submissions/75a63057-f8c7-4da0-b246-5de3e81077be

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
import Theorems.Thm_PaddedDescent_F_Arith_four_mul_nRect_le

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (g : ℕ) : Groundwork.Prog.nRect g ≤ g ^ 4 := by
  have := four_mul_nRect_le g
  omega
end PaddedDescent.F.Arith
