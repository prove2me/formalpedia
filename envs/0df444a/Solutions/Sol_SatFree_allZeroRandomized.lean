-- Prove2me | solution 1 for SatFree.allZeroRandomized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:10:35.141145+00:00
-- url     : https://prove2.me/submissions/526c2a35-0c48-4814-886b-d1646d2b8ce3

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
import Theorems.Thm_SatFree_allZero
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SatFree_randomnessHelps


set_option autoImplicit false
section
section
open SatFree
open Groundwork FreeCode
open scoped NNReal ENNReal
namespace SatFree
theorem _root_.solution : AllZeroRandomized := fun p hp k hk =>
  le_antisymm ((randomnessHelps p hp k).trans (le_of_eq (allZero.1 k hk))) bot_le
end SatFree
