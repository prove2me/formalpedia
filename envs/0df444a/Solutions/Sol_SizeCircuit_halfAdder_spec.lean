-- Prove2me | solution 1 for SizeCircuit.halfAdder_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:22:40.163817+00:00
-- url     : https://prove2.me/submissions/d98fd0cf-fd70-4e1a-b347-9b90e4fa8d6b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
import Theorems.Thm_CircuitLowerBound_Blocks_gval_and
import Theorems.Thm_CircuitLowerBound_Blocks_gval_xor


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution (v : ℕ → Bool) (N a u : ℕ) (h : Obeys v N (halfAdder a u)) :
    (v N).toNat + 2 * (v (N + 1)).toNat = (v a).toNat + (v u).toNat := by
  have h' : v N = gval v (opXor, a, u) ∧ v (N + 1) = gval v (opAnd, a, u) ∧ True := h
  obtain ⟨h0, h1, -⟩ := h'
  rw [gval_xor] at h0
  rw [gval_and] at h1
  rw [h0, h1]
  cases v a <;> cases v u <;> rfl
end SizeCircuit
