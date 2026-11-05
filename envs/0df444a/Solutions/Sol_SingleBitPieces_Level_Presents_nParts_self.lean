-- Prove2me | solution 1 for SingleBitPieces.Level.Presents.nParts_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:17:08.910686+00:00
-- url     : https://prove2.me/submissions/b538a050-546e-4470-86f2-e2a59ce20428

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecCrossing_Crossing
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_SingleBitPieces_SecCrossing_PolyA
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_Paper_SecLevel_Recursion
import Definitions.Def_ClauseBound_Alg_Grid
import Mathlib.Tactic
import Definitions.Def_SingleBitPieces_Level_Presents

set_option autoImplicit false
section
section
open SingleBitPieces SingleBitPieces.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped
open SingleBitPieces.Level.Presents
namespace SingleBitPieces.Level.Presents
theorem _root_.solution (g : ℕ) (tr : Bool) : nParts g g tr = g := by cases tr <;> rfl
end SingleBitPieces.Level.Presents
