-- Prove2me | solution 1 for SingleBitPieces.Level.Presents.time_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:10:09.328848+00:00
-- url     : https://prove2.me/submissions/882dd03f-7b35-4ab1-add6-941a572fbbdc

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
theorem _root_.solution (g B lm : ℕ) {t : ℕ} (hl : 1 ≤ lm) (ht : 1 ≤ t) : g * (t + 1) ≤ sideA g * (B + lm) ^ sideA g * t := by
  have h1 : 1 ≤ (B + lm) ^ sideA g := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 * g ≤ sideA g := by unfold sideA; omega
  calc g * (t + 1) ≤ g * (2 * t) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * g * 1 * t := by ring
    _ ≤ sideA g * (B + lm) ^ sideA g * t := Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 h1)
end SingleBitPieces.Level.Presents
