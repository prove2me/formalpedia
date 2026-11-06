-- Prove2me | solution 1 for SizeCircuit.length_formulaOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:08:13.461481+00:00
-- url     : https://prove2.me/submissions/277e8bbd-208e-4bf0-b3ad-68f456e19967

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_SizeCircuit_General
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Gamma
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length


section
namespace SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound CircuitLowerBound.Blocks ENP
private theorem length_zipIdx (n : ℕ) : ∀ (K : List GateD) (j : ℕ), ((K.zipIdx j).flatMap fun gt => gateClauses (n + gt.2) gt.1).length = 4 * K.length
  | [], j => rfl
  | g :: K, j => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, length_zipIdx n K (j + 1), List.length_cons]
    have h : (gateClauses (n + (g, j).2) (g, j).1).length = 4 := rfl
    rw [h]
    omega
end SizeCircuit
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound CircuitLowerBound.Blocks ENP
namespace SizeCircuit
theorem _root_.solution (n : ℕ) (K : List GateD) : (formulaOf n K).length = 4 * K.length + 1 := by
  rw [formulaOf, List.length_append, wiresFormula, length_zipIdx]
  rfl
end SizeCircuit
