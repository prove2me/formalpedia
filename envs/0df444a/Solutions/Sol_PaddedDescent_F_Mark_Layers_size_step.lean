-- Prove2me | solution 1 for PaddedDescent.F.Mark.Layers.size_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:49:25.824237+00:00
-- url     : https://prove2.me/submissions/de5889c9-b7b6-49b6-96c1-cebe50db444d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_PaddedDescent_F_MarkLayers
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog
open PaddedDescent.F.Mark.Layers
namespace PaddedDescent.F.Mark.Layers
theorem _root_.solution (κ N : ℕ) (h : 3 ^ κ ≤ 2 ^ N) : 3 * κ ≤ 2 * N + 3 := by
  have h1 : (2:ℕ) ^ (3 * (κ / 2)) ≤ 3 ^ (2 * (κ / 2)) := by
    rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left (by norm_num) _
  have h2 : (3:ℕ) ^ (2 * (κ / 2)) ≤ 3 ^ κ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2:ℕ) ^ (3 * (κ / 2)) ≤ 2 ^ N := h1.trans (h2.trans h)
  have h4 : 3 * (κ / 2) ≤ N := (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  omega
end PaddedDescent.F.Mark.Layers
