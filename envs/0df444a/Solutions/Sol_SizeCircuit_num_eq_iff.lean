-- Prove2me | solution 1 for SizeCircuit.num_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:41:25.7613+00:00
-- url     : https://prove2.me/submissions/9c719f9c-efbf-46b3-9dd0-703134d74c19

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Compare
import Theorems.Thm_SizeCircuit_testBit_num
import Theorems.Thm_CircuitLowerBound_Blocks_num_congr
import Theorems.Thm_CircuitLowerBound_Blocks_num_lt
import Theorems.Thm_CircuitLowerBound_Blocks_num_testBit
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.testBit



set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks
namespace SizeCircuit
theorem _root_.solution (b : ℕ → Bool) (L s : ℕ) : num b L = s ↔ s < 2 ^ L ∧ ∀ i < L, b i = s.testBit i := by
  constructor
  · rintro rfl
    exact ⟨num_lt b L, fun i hi => (testBit_num b L i hi).symm⟩
  · rintro ⟨h1, h2⟩
    rw [num_congr h2, num_testBit, Nat.mod_eq_of_lt h1]
end SizeCircuit
