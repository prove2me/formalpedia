-- Prove2me | solution 1 for SplitCount.size_lit_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:17:30.244264+00:00
-- url     : https://prove2.me/submissions/954ffad3-c256-47ef-82d8-aa05eec9af25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_Sizes
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_prod
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_prod



set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat
namespace SplitCount
theorem _root_.solution {l : ℕ × Bool} {n : ℕ} (h : l.1 < n) : size l ≤ n + 2 := by
  have : l.1.size ≤ n := Nat.size_le.2 (h.trans Nat.lt_two_pow_self)
  rw [size_prod, size_nat, size_bool]
  omega
end SplitCount
