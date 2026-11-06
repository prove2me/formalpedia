-- Prove2me | solution 1 for Printed.one_le_two_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:03:33.401113+00:00
-- url     : https://prove2.me/submissions/18045526-8791-4fcb-9bd9-f905c854a781

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
theorem _root_.solution {B : ℕ} (hB : 1 ≤ B) : (1 : ℤ) ≤ 2 ^ B - 1 := by
  have h2 : (2 : ℤ) ^ 1 ≤ 2 ^ B := pow_le_pow_right₀ (by norm_num) hB
  rw [pow_one] at h2
  linarith
end Printed
