-- Prove2me | solution 1 for Printed.stDecides
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:04:26.783587+00:00
-- url     : https://prove2.me/submissions/8b1df77c-b551-4157-94a4-37080fd14e85

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
import Theorems.Thm_Printed_stAlgorithm
import Theorems.Thm_Enumerate_stEnumeration
import Theorems.Thm_Exits_stAlgorithm
import Theorems.Thm_Printed_stDecides_of


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution : StDecides := stDecides_of stAlgorithm Enumerate.stEnumeration
end Printed
