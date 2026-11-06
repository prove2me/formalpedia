-- Prove2me | solution 1 for SizeCircuit.wfa_halfAdder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:23:01.427198+00:00
-- url     : https://prove2.me/submissions/949d99fc-f2d4-4ad1-8651-34b1977a3839

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
theorem _root_.solution {N a u : ℕ} (ha : a < N) (hu : u < N) : WFa N (halfAdder a u) := by
  have h : (a < N ∧ u < N) ∧ (a < N + 1 ∧ u < N + 1) ∧ True := by
    refine ⟨?_, ?_, trivial⟩ <;> omega
  exact h
end SizeCircuit
