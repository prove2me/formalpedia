-- Prove2me | solution 1 for SizeCircuit.fullAdder_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:30:47.494147+00:00
-- url     : https://prove2.me/submissions/2bf33f17-599a-4dd6-8ad6-1f0ade2eaa49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
import Theorems.Thm_CircuitLowerBound_Blocks_gval_and
import Theorems.Thm_CircuitLowerBound_Blocks_gval_or
import Theorems.Thm_CircuitLowerBound_Blocks_gval_xor


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution (v : ℕ → Bool) (N a u w : ℕ) (h : Obeys v N (fullAdder N a u w)) :
    (v (N + 1)).toNat + 2 * (v (N + 4)).toNat = (v a).toNat + (v u).toNat + (v w).toNat := by
  have h' : v N = gval v (opXor, a, u) ∧ v (N + 1) = gval v (opXor, N, w) ∧ v (N + 2) = gval v (opAnd, a, u) ∧ v (N + 3) = gval v (opAnd, N, w) ∧
      v (N + 4) = gval v (opOr, N + 2, N + 3) ∧ True := h
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := h'
  rw [gval_xor] at h0 h1
  rw [gval_and] at h2 h3
  rw [gval_or] at h4
  rw [h1, h4, h2, h3, h0]
  cases v a <;> cases v u <;> cases v w <;> rfl
end SizeCircuit
