-- Prove2me | solution 1 for SizeCircuit.wfa_fullAdder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:22:32.793902+00:00
-- url     : https://prove2.me/submissions/b6eed2ec-28ec-419d-92f6-1f20ad043aab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition

set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution {N a u w : ℕ} (ha : a < N) (hu : u < N) (hw : w < N) : WFa N (fullAdder N a u w) := by
  have h : (a < N ∧ u < N) ∧ (N < N + 1 ∧ w < N + 1) ∧ (a < N + 2 ∧ u < N + 2) ∧ (N < N + 3 ∧ w < N + 3) ∧ (N + 2 < N + 4 ∧ N + 3 < N + 4) ∧ True := by
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega
  exact h
end SizeCircuit
