-- Prove2me | solution 1 for Printed.stHalf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:26:43.394556+00:00
-- url     : https://prove2.me/submissions/7ae45034-faa4-4c0e-bb82-fb01cd93fc26

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
import Theorems.Thm_Printed_achievable_half
import Theorems.Thm_Printed_half_mem
import Theorems.Thm_Printed_eStar_le
import Theorems.Thm_Printed_eStar_nonneg
import Theorems.Thm_Paper_achievable_half
import Theorems.Thm_Paper_eStar_le
import Theorems.Thm_Paper_eStar_nonneg


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
namespace Printed
theorem _root_.solution : StHalf := ⟨fun _ hK => achievable_half hK, eStar_le half_mem, eStar_nonneg⟩
end Printed
