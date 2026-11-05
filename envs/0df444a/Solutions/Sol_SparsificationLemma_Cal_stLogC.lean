-- Prove2me | solution 1 for SparsificationLemma.Cal.stLogC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:22:18.663422+00:00
-- url     : https://prove2.me/submissions/9962e556-b43f-4f49-8b8b-a183922bfcd5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Theorems.Thm_SparsificationLemma_Cal_clog_eq_ceil_logb
import Theorems.Thm_SparsificationLemma_Cal_le_xC_of_two_le

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution : StLogC := by
  intro k ε hk h0 h1
  exact clog_eq_ceil_logb (by linarith [le_xC_of_two_le hk h0 h1])
end SparsificationLemma.Cal
