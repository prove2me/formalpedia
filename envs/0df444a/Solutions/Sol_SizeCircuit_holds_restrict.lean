-- Prove2me | solution 1 for SizeCircuit.holds_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:09:08.316951+00:00
-- url     : https://prove2.me/submissions/d4417a5d-aa65-4a0e-81d4-dc887125feac

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_SizeCircuit_General
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Gamma
import Theorems.Thm_SizeCircuit_ext_of_lt
import Theorems.Thm_SizeCircuit_holds_congr


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound CircuitLowerBound.Blocks ENP
namespace SizeCircuit
theorem _root_.solution {n m : ℕ} (b : Fin (n + m) → Bool) (x : Fin n → Bool) (hbx : ∀ i, b (Fin.castAdd m i) = x i) {ψ : Fml}
    (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) : Holds (ext b) ψ ↔ Holds (ext x) ψ :=
  holds_congr fun C hC l hl => by
    have h := hψ C hC l hl
    rw [ext_of_lt b (by omega : l.1 < n + m), ext_of_lt x h]
    exact hbx ⟨l.1, h⟩
end SizeCircuit
