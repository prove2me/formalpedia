-- Prove2me | solution 1 for P2M_Eight_Level_value_netOf__39744228d791
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:10:36.379291+00:00
-- url     : https://prove2.me/submissions/dcd05a8d-65a0-4632-9831-0c585a672905

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_Eight_Level_digOf_le
import Theorems.Thm_P2M_Eight_Level_Z__digOf_6fd272fe669a
import Theorems.Thm_P2M_Eight_Level_netOf__row_07c080f825b3
import Theorems.Thm_P2M_Eight_Level_netOf__col_8a246f415134
import Theorems.Thm_ClauseBound_Alg_GridNet_stC_full
import Theorems.Thm_Eight_value_colNetwork
import Theorems.Thm_Eight_value_rowNetwork
import Theorems.Thm_Groundwork_Grid_stC_full
import Theorems.Thm_Groundwork_Network_value_pull
import Theorems.Thm_Paper_mem_rectangles


set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}
namespace Eight.Level
theorem _root_.solution (hlam : 1 ≤ lam) (g : ℕ) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    (netOfι g tr lam y Rm).value = Zι (gridR0 g g lam Rm) (Eight.Level.patOf g lam y) := by
  rw [← Zι_digOf]
  cases tr
  · rw [netOfι_row, ← value_rowNetwork hlam (gridR0 g g lam Rm) (digOf_le g lam y)]
    exact Network.value_pull (rowNetwork (gridR0 g g lam Rm) (digOf g lam y)) _ _ _ fun _ => stC_full g g false lam
  · rw [netOfι_col, ← value_colNetwork hlam (gridR0 g g lam Rm) (digOf_le g lam y)]
    exact Network.value_pull (colNetwork (gridR0 g g lam Rm) (digOf g lam y)) _ _ _ fun _ => stC_full g g true lam
end Eight.Level
