-- Prove2me | solution 1 for Printed.stAlgorithm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:02.791928+00:00
-- url     : https://prove2.me/submissions/6d41fde7-7aa8-4f24-963c-d476dacbbb85

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
import Theorems.Thm_Printed_stCountCost
import Theorems.Thm_Exits_stCountCost
import Theorems.Thm_Printed_stAlgorithm_of
import Theorems.Thm_Suffices_stSuffices


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution : StAlgorithm := stAlgorithm_of Suffices.stSuffices stCountCost
end Printed
