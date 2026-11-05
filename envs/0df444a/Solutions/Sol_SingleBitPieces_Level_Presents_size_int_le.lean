-- Prove2me | solution 1 for SingleBitPieces.Level.Presents.size_int_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:10:08.202362+00:00
-- url     : https://prove2.me/submissions/c21f846f-26e0-49cb-a37d-40489314bd24

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
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_size_int
attribute [local simp] Groundwork.size_int



set_option autoImplicit false
section
section
open SingleBitPieces SingleBitPieces.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped
open SingleBitPieces.Level.Presents
namespace SingleBitPieces.Level.Presents
theorem _root_.solution {v : ℤ} {b : ℕ} (h : |v| ≤ 2 ^ b) : size v ≤ b + 2 := by
  rw [size_int]
  have h1 : v.natAbs ≤ 2 ^ b := by
    have : ((v.natAbs : ℕ) : ℤ) ≤ ((2 ^ b : ℕ) : ℤ) := by rw [Int.natCast_natAbs]; exact_mod_cast h
    exact_mod_cast this
  have h2 : v.natAbs < 2 ^ (b + 1) := lt_of_le_of_lt h1 (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have := Nat.size_le.2 h2
  omega
end SingleBitPieces.Level.Presents
