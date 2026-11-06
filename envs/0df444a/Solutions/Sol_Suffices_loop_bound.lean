-- Prove2me | solution 1 for Suffices.loop_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:46:12.290505+00:00
-- url     : https://prove2.me/submissions/54a6ed10-5990-41a3-a926-86c0c1b9bd92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Defs
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Tactic.Ring
import Definitions.Def_Suffices_Sizes
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog CountKSat Exits
namespace Suffices
theorem _root_.solution (D N : ℕ) (hN : 1 ≤ N) : (143 * (D + 1) + 1) * N ^ 3 + 4 ≤ (143 * (D + 1) + 5) * N ^ (143 * (D + 1) + 5) := by
  have e3 : N ^ 3 ≤ N ^ (143 * (D + 1) + 5) := Nat.pow_le_pow_right hN (by omega)
  have hN3 : 1 ≤ N ^ 3 := Nat.one_le_pow _ _ hN
  have a : (143 * (D + 1) + 5) * N ^ 3 ≤ (143 * (D + 1) + 5) * N ^ (143 * (D + 1) + 5) := Nat.mul_le_mul_left _ e3
  have e : (143 * (D + 1) + 5) * N ^ 3 = (143 * (D + 1) + 1) * N ^ 3 + 4 * N ^ 3 := by ring
  omega
end Suffices
