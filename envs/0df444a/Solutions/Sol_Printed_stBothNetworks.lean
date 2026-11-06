-- Prove2me | solution 1 for Printed.stBothNetworks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:47:48.47793+00:00
-- url     : https://prove2.me/submissions/4a5b6b71-0e74-412f-9247-900e704f18db

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelSentences
import Definitions.Def_Printed_LevelPoly
import Definitions.Def_Printed_GroupingPoly
import Definitions.Def_Printed_LevelFrom
import Theorems.Thm_Printed_stAskServes
import Theorems.Thm_Printed_stBothNetworks_of


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution : StBothNetworks := stBothNetworks_of stAskServes
end Printed
