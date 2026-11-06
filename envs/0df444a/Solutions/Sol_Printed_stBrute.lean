-- Prove2me | solution 1 for Printed.stBrute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:40:18.395868+00:00
-- url     : https://prove2.me/submissions/90221352-64c5-45e8-8f69-a51bb91227e0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_Printed_Absorb
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic
import Definitions.Def_Printed_Achievable
import Theorems.Thm_Printed_bruteMachine_poly
import Theorems.Thm_Printed_bruteMachine_achieves

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
namespace Printed
theorem _root_.solution : StBrute := fun K hK => ⟨bruteMachine_poly K, bruteMachine_achieves K hK⟩
end Printed
