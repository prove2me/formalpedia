-- Prove2me | solution 1 for Suffices.stSuffices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:25:12.370072+00:00
-- url     : https://prove2.me/submissions/076ca0d8-419f-4963-ab91-9bd0ec0eb1d7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Loop
import Definitions.Def_Suffices_Total
import Definitions.Def_Exits_Poly
import Definitions.Def_CountKSat_InOut
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Suffices_Main
import Theorems.Thm_Suffices_stSufficesOf
import Theorems.Thm_Exits_stFoldUntilPoly
import Theorems.Thm_Suffices_stLoopRuns
import Theorems.Thm_Suffices_stTotal


set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
namespace Suffices
theorem _root_.solution : StSuffices := stSufficesOf stLoopRuns stTotal stFoldUntilPoly
end Suffices
