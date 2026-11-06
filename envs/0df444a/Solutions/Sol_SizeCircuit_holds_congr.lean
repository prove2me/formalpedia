-- Prove2me | solution 1 for SizeCircuit.holds_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:17:36.576685+00:00
-- url     : https://prove2.me/submissions/b50b188c-370e-4691-9c9b-2a5136083647

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_CircuitLowerBound_Circ_Form
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_General

set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat CircuitLowerBound CircuitLowerBound.Blocks ENP
namespace SizeCircuit
theorem _root_.solution {a a' : ℕ → Bool} {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, a l.1 = a' l.1) : Holds a ψ ↔ Holds a' ψ := by
  constructor
  · intro H C hC
    obtain ⟨l, hl, e⟩ := H C hC
    exact ⟨l, hl, by rw [← h C hC l hl]; exact e⟩
  · intro H C hC
    obtain ⟨l, hl, e⟩ := H C hC
    exact ⟨l, hl, by rw [h C hC l hl]; exact e⟩
end SizeCircuit
