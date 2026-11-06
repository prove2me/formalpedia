-- Prove2me | solution 1 for Sat3Graph.size_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:36:36.548204+00:00
-- url     : https://prove2.me/submissions/443c1cce-20e2-4ede-a51e-684e003da7e9

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
theorem _root_.solution {c c' : ℕ} (hc : c ≤ c') (n : ℕ) : c * (n + 2) ^ c ≤ c' * (n + 2) ^ c' :=
  Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hc)
end Sat3Graph
