-- Prove2me | solution 1 for PairsToBound.widthOr3Stmt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:11:47.24168+00:00
-- url     : https://prove2.me/submissions/9706b8db-2e06-4bc7-87c9-95cd3fb0186d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Width
import Theorems.Thm_PairsToBound_three_le_widthOr3
import Theorems.Thm_PairsToBound_length_le_widthOr3
import Theorems.Thm_PairsToBound_widthOr3_le_max
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open PairsToBound
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution : WidthOr3Stmt := by
  intro n φ
  refine ⟨three_le_widthOr3 φ, fun hnd => ⟨fun C hC => length_le_widthOr3 hC, hnd⟩, fun k hk hφ => ?_⟩
  have h1 : widthOr3 φ ≤ max k 3 := widthOr3_le_max hφ.1
  have h2 : widthOr3 φ ≤ 3 * k := h1.trans (max_le (by omega) (by omega))
  refine ⟨h1, ?_⟩
  calc widthOr3 φ ^ 2 ≤ (3 * k) ^ 2 := Nat.pow_le_pow_left h2 2
    _ = 9 * k ^ 2 := by ring
end PairsToBound
