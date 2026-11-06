-- Prove2me | solution 1 for Printed.threeSat_through_eStar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:57:55.325721+00:00
-- url     : https://prove2.me/submissions/38932573-42c7-44dd-b426-c22ec7db9691

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Proof
import Definitions.Def_Printed_LevelFrom
import Definitions.Def_Printed_Grouping
import Definitions.Def_Variance_Grouping
import Definitions.Def_Exits_End
import Definitions.Def_Value_End
import Definitions.Def_Suffices_Main
import Definitions.Def_Enumerate_Enumeration
import Definitions.Def_Printed_End
import Theorems.Thm_Printed_stEveryEta
import Theorems.Thm_Printed_stProofNamed
import Theorems.Thm_Enumerate_stEnumeration
import Theorems.Thm_Exits_stProofNamed
import Theorems.Thm_Printed_threeSat_through_eStar_of


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution : Sat3.ThmEveryDelta := threeSat_through_eStar_of stEveryEta Enumerate.stEnumeration stProofNamed
end Printed
