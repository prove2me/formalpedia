-- Prove2me | solution 1 for SatFree.sethGivesSomeK
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:21:40.768217+00:00
-- url     : https://prove2.me/submissions/ac525ad8-0ada-4e3d-88c2-bb724cf4542c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
import Definitions.Def_FreeCode_Order
set_option autoImplicit false
section
section
open SatFree
open scoped NNReal ENNReal

theorem solution : SethGivesSomeK := by
  intro hseth
  by_contra hnone
  push_neg at hnone
  have hz : SatFree.sInfty = 0 := by
    apply le_antisymm
    · apply iSup_le
      intro k
      apply iSup_le
      intro hk
      exact hnone k hk
    · exact bot_le
  rw [hseth] at hz
  norm_num at hz
