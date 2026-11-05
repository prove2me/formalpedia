-- Prove2me | solution 1 for Value.stCliqueValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:50:47.135937+00:00
-- url     : https://prove2.me/submissions/a3541fb7-0de6-48de-9836-2c683e85ca47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_Value_Clique
import Theorems.Thm_Value_stSumOverSettings
import Theorems.Thm_Value_stCopiesMustAgree
import Theorems.Thm_Value_stOneStringPerEdge
import Theorems.Thm_Value_stCliqueValueOf

set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Finset Eight.SecNetworks
namespace Value
theorem _root_.solution : StCliqueValue := stCliqueValueOf stSumOverSettings stCopiesMustAgree stOneStringPerEdge
end Value
