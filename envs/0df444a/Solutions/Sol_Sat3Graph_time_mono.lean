-- Prove2me | solution 1 for Sat3Graph.time_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:42:09.036034+00:00
-- url     : https://prove2.me/submissions/b2ba265d-ecda-4037-bf6d-f3269952eea7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_GraphProblems_Read
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Host

set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog GraphProblems Paper SplitSat
namespace Sat3Graph
theorem _root_.solution {c c' : ℕ} {δ δ' : ℝ} (hδ : δ ≤ δ') (hc : c ≤ c') (n : ℕ) : (c : ℝ) * (2 : ℝ) ^ (δ * n) ≤ c' * (2 : ℝ) ^ (δ' * n) := by
  have h1 : (c : ℝ) ≤ c' := by exact_mod_cast hc
  have h2 : (2 : ℝ) ^ (δ * n) ≤ (2 : ℝ) ^ (δ' * n) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n))
  exact mul_le_mul h1 h2 (by positivity) (Nat.cast_nonneg _)
end Sat3Graph
