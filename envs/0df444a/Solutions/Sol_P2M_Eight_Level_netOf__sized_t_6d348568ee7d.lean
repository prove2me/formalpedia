-- Prove2me | solution 1 for P2M_Eight_Level_netOf__sized_t_6d348568ee7d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:19:20.698369+00:00
-- url     : https://prove2.me/submissions/97b9a9c6-fea8-46c5-b286-2b87572dbd3c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_Eight_Level_digOf_le
import Theorems.Thm_P2M_Eight_Level_netOf__row_07c080f825b3
import Theorems.Thm_P2M_Eight_Level_netOf__col_8a246f415134
import Theorems.Thm_ClauseBound_Alg_GridNet_abs_gridR_le
import Theorems.Thm_Eight_colNetwork_sized_t
import Theorems.Thm_Eight_rowNetwork_sized_t
import Theorems.Thm_Groundwork_Network_sized_pull_of_le
import Theorems.Thm_Paper_mem_rectangles


set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}
namespace Eight.Level
theorem _root_.solution {B : ℕ} (hlam : 1 ≤ lam) (g : ℕ) (tr : Bool) (y : ℕ) {Rm : Inst (Fin (g * g)) (List Bool)} (hR : BoundedInst lam B Rm) :
    (netOfι g tr lam y Rm).Sized (g ^ 3 * lam) (g * B + g ^ 2 * tOf lam) := by
  have hW : ∀ w h, |gridR0 g g lam Rm w h| ≤ 2 ^ B := abs_gridR_le false hR
  cases tr
  · rw [netOfι_row]
    exact Network.sized_pull_of_le (rowNetwork (gridR0 g g lam Rm) (digOf g lam y)) _ _ _ (rowNetwork_sized_t hlam _ hW (digOf_le g lam y)) fun _ => le_of_eq (by ring)
  · rw [netOfι_col]
    exact Network.sized_pull_of_le (colNetwork (gridR0 g g lam Rm) (digOf g lam y)) _ _ _ (colNetwork_sized_t hlam _ hW (digOf_le g lam y)) fun _ => le_of_eq (by ring)
end Eight.Level
