-- Prove2me | solution 1 for Printed.size_under
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:23:53.298609+00:00
-- url     : https://prove2.me/submissions/e90335b1-30ce-4d38-b2f9-2c5aed4ff406

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Count
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines
namespace Printed
theorem _root_.solution (s P C₁ : ℕ) : s + C₁ * (P + 1) ^ C₁ + 4 ≤ (3 * C₁ + 5) * (s + P + 1) ^ (3 * C₁ + 5) := by
  have p1 : s + P + 1 ≤ (s + P + 1) ^ (3 * C₁ + 5) := Nat.le_self_pow (by omega) _
  have p2 : (P + 1) ^ C₁ ≤ (s + P + 1) ^ (3 * C₁ + 5) := (Nat.pow_le_pow_left (by omega) C₁).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have p3 := Nat.mul_le_mul_left C₁ p2
  have e : (3 * C₁ + 5) * (s + P + 1) ^ (3 * C₁ + 5) = 5 * (s + P + 1) ^ (3 * C₁ + 5) + C₁ * (s + P + 1) ^ (3 * C₁ + 5) + 2 * (C₁ * (s + P + 1) ^ (3 * C₁ + 5)) := by ring
  omega
end Printed
