-- Prove2me | solution 1 for Printed.poly_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:12:16.682716+00:00
-- url     : https://prove2.me/submissions/9654d4ab-ed9c-402a-92d8-b9a9152a9116

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
namespace Printed
theorem _root_.solution {D M k c X : ℕ} (hX : 1 ≤ X) (hk : k ≤ c) (h1 : 1 ≤ c) (hc : D + M ≤ c) : D * X + M * X ^ k ≤ c * X ^ c :=
  calc D * X + M * X ^ k ≤ D * X ^ c + M * X ^ c := Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) X)) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX hk))
    _ = (D + M) * X ^ c := by ring
    _ ≤ c * X ^ c := Nat.mul_le_mul_right _ hc
end Printed
