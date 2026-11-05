-- Prove2me | solution 1 for P2M_Eight_Level_netOf__S_6e5e490549e4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:24:12.324207+00:00
-- url     : https://prove2.me/submissions/9b37dd45-cc2d-4451-bdaf-45e28e2cd144

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_P2M_Eight_Level_netOf__row_07c080f825b3
import Theorems.Thm_P2M_Eight_Level_netOf__col_8a246f415134
import Theorems.Thm_Paper_mem_rectangles


set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}
namespace Eight.Level
theorem _root_.solution (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (a : Fin (nParts g g tr)) :
    (netOfι g tr lam y Rm).S a = words (g ^ 3 * lam) := by
  have e : g * (g * g) * lam = g ^ 3 * lam := by ring
  cases tr
  · rw [netOfι_row, ← e]
    rfl
  · rw [netOfι_col, ← e]
    rfl
end Eight.Level
