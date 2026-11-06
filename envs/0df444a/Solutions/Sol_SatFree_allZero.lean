-- Prove2me | solution 1 for SatFree.allZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:00:10.026211+00:00
-- url     : https://prove2.me/submissions/e8bef8c8-9b3e-4101-8133-cf3f9f331d78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Reader
import Definitions.Def_FreeCode_Order
import Definitions.Def_FreeCode_Random
import Definitions.Def_FreeCode_Behind
import Definitions.Def_FreeCode_Brute
import Definitions.Def_FreeCode_Tied
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Main
import Theorems.Thm_FreeCode_allZeroFrom
import Theorems.Thm_FreeCode_stTied
import Theorems.Thm_FreeCode_stTiedThree


set_option autoImplicit false
section
section
open SatFree
open Groundwork FreeCode
open scoped NNReal ENNReal
namespace SatFree
theorem _root_.solution : AllZero := FreeCode.allZeroFrom stTiedThree stTied
end SatFree
