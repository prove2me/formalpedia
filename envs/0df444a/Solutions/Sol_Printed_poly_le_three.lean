-- Prove2me | solution 1 for Printed.poly_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:29:47.402393+00:00
-- url     : https://prove2.me/submissions/447fc5d4-ab04-465f-89a2-2f3fc6c63cb4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Eight_ViaGrouping_Main
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingRun

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution {D M M' k k' c X : ℕ} (hX : 1 ≤ X) (hk : k ≤ c) (hk' : k' ≤ c) (h1 : 1 ≤ c) (hc : D + M + M' ≤ c) : D * X + M * X ^ k + M' * X ^ k' ≤ c * X ^ c :=
  calc D * X + M * X ^ k + M' * X ^ k' ≤ D * X ^ c + M * X ^ c + M' * X ^ c :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) X)) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX hk))) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX hk'))
    _ = (D + M + M') * X ^ c := by ring
    _ ≤ c * X ^ c := Nat.mul_le_mul_right _ hc
end Printed
