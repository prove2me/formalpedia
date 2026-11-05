-- Prove2me | solution 1 for SingleBitPieces.Level.Presents.f_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:34:08.169624+00:00
-- url     : https://prove2.me/submissions/5afe7701-9911-4bba-8c91-61de1a626b74

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
import Theorems.Thm_ClauseBound_Alg_GridPresents_gridFf_eq
import Theorems.Thm_ClauseBound_Alg_GridPresents_gridN_f
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SingleBitPieces SingleBitPieces.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped
open SingleBitPieces.Level.Presents
namespace SingleBitPieces.Level.Presents
theorem _root_.solution (P : PiecesF) {g : ℕ} (tr : Bool) (ℓ y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z θ : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * ℓ) (hθ : θ.length = capG P g g tr 0 ℓ y a b) :
    gridFf P [] g g tr 0 ℓ y ((a.val, b.val), (z, θ)) = (gridN P [] g g tr 0 ℓ y Rm).f a b z θ := by
  rw [gridFf_eq, gridN_f P [] g g tr 0 ℓ y Rm hab hz hθ]
end SingleBitPieces.Level.Presents
