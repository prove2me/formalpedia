-- Prove2me | solution 1 for Printed.stCountCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:51:18.961379+00:00
-- url     : https://prove2.me/submissions/90299c5e-e62d-4587-a4d1-e529495dae43

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
import Theorems.Thm_Printed_stGroupingTied
import Theorems.Thm_Printed_stClique
import Theorems.Thm_Exits_stClique
import Theorems.Thm_Printed_stCountCost_of
import Theorems.Thm_Printed_stGroupingPoly
import Theorems.Thm_Printed_stOnProcedures


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution : StCountCost := stCountCost_of stClique stGroupingTied stGroupingPoly stOnProcedures
end Printed
