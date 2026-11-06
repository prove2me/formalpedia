-- Prove2me | solution 1 for SizeCircuit.gval_digit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:25:06.336719+00:00
-- url     : https://prove2.me/submissions/c85f5f99-68ea-4ebb-ba6e-a245a750290a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Compare
import Theorems.Thm_CircuitLowerBound_Blocks_gval_and
import Theorems.Thm_CircuitLowerBound_Blocks_gval_andN


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution (v : ℕ → Bool) (t : Bool) (i j : ℕ) : gval v ((if t then opAnd else opAndN), i, j) = (v i && (v j == t)) := by
  cases t
  · rw [if_neg Bool.false_ne_true, gval_andN]
    cases v i <;> cases v j <;> rfl
  · rw [if_pos rfl, gval_and]
    cases v i <;> cases v j <;> rfl
end SizeCircuit
