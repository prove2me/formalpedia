-- Prove2me | solution 1 for PairsToBound.start_le_foldr_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:48:22.077824+00:00
-- url     : https://prove2.me/submissions/060d4eb4-ebc4-4766-98e7-c16f3b0de813

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_SparsificationLemma_StepSparsify
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Width
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open PairsToBound
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution (l : List ℕ) (a : ℕ) : a ≤ l.foldr max a := by
  induction l with
  | nil => exact le_rfl
  | cons b l ih => exact ih.trans (le_max_right _ _)
end PairsToBound
