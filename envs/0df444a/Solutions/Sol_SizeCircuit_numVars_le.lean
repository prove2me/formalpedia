-- Prove2me | solution 1 for SizeCircuit.numVars_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:16:43.059663+00:00
-- url     : https://prove2.me/submissions/eddeeee9-4172-4bd7-9037-22547ad8b2cb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_SizeCircuit_Gamma
import Definitions.Def_GraphProblems_Sized
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Sized
import Theorems.Thm_SizeCircuit_stGamma


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight
namespace SizeCircuit
theorem _root_.solution {gates : ℕ → ℕ → List GateD} {a : ℕ} (hT : TestsSize gates a) (n s : ℕ) : numVars gates n s ≤ (a + 1) * (n + 1) := by
  unfold numVars
  split_ifs with h0
  · exact Nat.zero_le _
  · exact (stGamma gates a hT n s (by omega)).2.1
end SizeCircuit
