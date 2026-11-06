-- Prove2me | solution 1 for SizeCircuit.gval_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:24:58.984672+00:00
-- url     : https://prove2.me/submissions/fd8e2111-66bb-4dbb-a013-9cc7c03765b2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Compare
import Theorems.Thm_CircuitLowerBound_Blocks_gval_one
import Theorems.Thm_CircuitLowerBound_Blocks_gval_zero


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution (v : ℕ → Bool) (c : Prop) [Decidable c] (i j : ℕ) : gval v ((if c then opOne else opZero), i, j) = decide c := by
  by_cases h : c
  · rw [if_pos h, gval_one, decide_eq_true h]
  · rw [if_neg h, gval_zero, decide_eq_false h]
end SizeCircuit
