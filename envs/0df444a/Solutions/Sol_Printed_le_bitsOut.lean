-- Prove2me | solution 1 for Printed.le_bitsOut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:12:15.579205+00:00
-- url     : https://prove2.me/submissions/03035682-2608-49de-93a9-cb3b6f50e26d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Achievable
import Definitions.Def_Eight_ViaGrouping_Display
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingEntry

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
variable {C : Type} [HasSize C] {g K : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
namespace Printed
theorem _root_.solution {K : ℕ} (hK0 : 0 < K) (g P B : ℕ) : P * (2 * g / K) + g ^ 2 * B ≤ bitsOut K g P B := by
  unfold bitsOut
  refine Nat.add_le_add_right ?_ _
  rw [Nat.le_div_iff_mul_le hK0]
  calc P * (2 * g / K) * K = P * (2 * g / K * K) := Nat.mul_assoc _ _ _
    _ ≤ P * (2 * g) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
    _ = 2 * (g * P) := by ring
    _ ≤ 2 * (g * P) + (K - 1) := Nat.le_add_right _ _
end Printed
