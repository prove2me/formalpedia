-- Prove2me | solution 1 for P2M_Groundwork_PB_id__8af0b594aff4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:22:49.802347+00:00
-- url     : https://prove2.me/submissions/4d18cd4f-6d60-4592-bfb4-d4c83b890712

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Monotone.Basic
import Definitions.Def_ToTuring_Bound

set_option autoImplicit false
section
section
open Groundwork
open Groundwork.PB
variable {t s : ℕ → ℕ}
namespace Groundwork.PB
theorem _root_.solution : PB fun n => n := by
  refine ⟨1, fun n => ?_⟩
  rw [pow_one, Nat.one_mul]
  exact Nat.le_succ n
end Groundwork.PB
