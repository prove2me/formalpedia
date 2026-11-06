-- Prove2me | solution 1 for Printed.stClique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:30.324709+00:00
-- url     : https://prove2.me/submissions/68311af9-e7da-41e4-90e5-3b7b30e15779

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
import Theorems.Thm_Printed_stLevelTied
import Theorems.Thm_Printed_stBrute
import Theorems.Thm_Printed_stClique_of
import Theorems.Thm_Printed_stLevelPoly


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution : StClique := stClique_of stBrute stLevelTied stLevelPoly
end Printed
