-- Prove2me | solution 1 for SplitCount.size_nat_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:40:33.58923+00:00
-- url     : https://prove2.me/submissions/c004ba03-0599-4e85-9dbb-7aab7540742a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_Sizes
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_size_nat
attribute [local simp] Groundwork.size_nat



set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat
namespace SplitCount
theorem _root_.solution {v B : ℕ} (h : v < 2 ^ B) : size v ≤ B + 1 := by
  have : v.size ≤ B := Nat.size_le.2 h
  rw [size_nat]
  omega
end SplitCount
