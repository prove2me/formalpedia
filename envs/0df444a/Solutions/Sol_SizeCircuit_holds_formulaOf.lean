-- Prove2me | solution 1 for SizeCircuit.holds_formulaOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:22:20.411585+00:00
-- url     : https://prove2.me/submissions/92d7be52-da2b-4890-897b-73dd5a39677b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_SizeCircuit_General
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Gamma
import Theorems.Thm_CountKSat_StepCount_holds_append
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_SizeCircuit_holds_append
import Theorems.Thm_SizeCircuit_holds_cons
import Theorems.Thm_SizeCircuit_holds_nil
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound CircuitLowerBound.Blocks ENP
namespace SizeCircuit
theorem _root_.solution (a : ℕ → Bool) (n : ℕ) (K : List GateD) : Holds a (formulaOf n K) ↔ Holds a (wiresFormula n K) ∧ a (n + K.length - 1) = true := by
  rw [formulaOf, holds_append, holds_cons]
  constructor
  · rintro ⟨h1, ⟨l, hl, h2⟩, -⟩
    rw [List.mem_singleton.1 hl] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, ⟨_, List.mem_singleton.2 rfl, h2⟩, holds_nil a⟩
end SizeCircuit
