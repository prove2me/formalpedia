-- Prove2me | solution 1 for SatFree.toN_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:16:04.246518+00:00
-- url     : https://prove2.me/submissions/26c48fa3-882a-43ef-9d93-5f186441cb96

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

set_option autoImplicit false
section
section
open SatFree
open Groundwork FreeCode
open scoped NNReal ENNReal
namespace SatFree
theorem _root_.solution {n : ℕ} : Function.Injective (Decode.toN (n := n)) := by
  unfold Decode.toN
  refine List.map_injective_iff.2 (List.map_injective_iff.2 fun a b e => ?_)
  exact Prod.ext (Fin.ext (Prod.mk.inj e).1) (Prod.mk.inj e).2
end SatFree
