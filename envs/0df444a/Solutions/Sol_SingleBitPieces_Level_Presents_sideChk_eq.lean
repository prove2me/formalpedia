-- Prove2me | solution 1 for SingleBitPieces.Level.Presents.sideChk_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:10:07.161187+00:00
-- url     : https://prove2.me/submissions/4d247780-54b9-4610-bad2-aadd26b4628a

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
import Theorems.Thm_SingleBitPieces_Level_Presents_nMemb_self

set_option autoImplicit false
section
section
open SingleBitPieces SingleBitPieces.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped
open SingleBitPieces.Level.Presents
namespace SingleBitPieces.Level.Presents
theorem _root_.solution {C : Type} (g : ℕ) (tr : Bool) (lam : C → ℕ) (c : C) (y a : ℕ) (z : List Bool) :
    sideChk g tr lam ((c, y), (a, z)) = chkG g g tr (lam c) (a, z) := by
  unfold sideChk chkG
  rw [nMemb_self]
  rfl
end SingleBitPieces.Level.Presents
