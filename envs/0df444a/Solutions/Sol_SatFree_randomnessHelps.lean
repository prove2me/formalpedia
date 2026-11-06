-- Prove2me | solution 1 for SatFree.randomnessHelps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:13:30.355245+00:00
-- url     : https://prove2.me/submissions/975034a2-7383-495f-8d9c-52ec3495afe6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
import Definitions.Def_FreeCode_Random
import Theorems.Thm_SatFree_inTimeRand_of_inTime

set_option autoImplicit false
section
section
open SatFree
open Turing
open Sat3 (CNF Satisfiable)
open scoped NNReal ENNReal
namespace SatFree
theorem _root_.solution : RandomnessHelps := fun _ hp _ => le_iInf₂ fun δ hδ => iInf₂_le δ (inTimeRand_of_inTime hp hδ)
end SatFree
