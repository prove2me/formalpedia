-- Prove2me | solution 1 for P2M_Eight_Level_netOf__col_8a246f415134
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:00:55.738923+00:00
-- url     : https://prove2.me/submissions/abc7d817-63f7-4f4a-885d-2b3668f43022

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_Paper_mem_rectangles


set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}
namespace Eight.Level
theorem _root_.solution (g lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    netOfι g true lam y Rm = (colNetwork (gridR0 g g lam Rm) (digOf g lam y)).pull (fun _ => g * (g * g) * lam) (fun _ => stC g g true lam)
      (gridCl eightF [] g g true 0 lam y (gridR g g true lam Rm)) := rfl
end Eight.Level
