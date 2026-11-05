-- Prove2me | solution 1 for P2M_Eight_Level_netOf__row_07c080f825b3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:57:27.028211+00:00
-- url     : https://prove2.me/submissions/9944ee08-eec6-4684-a79e-3ae3fc9cc46c

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
    netOfι g false lam y Rm = (rowNetwork (gridR0 g g lam Rm) (digOf g lam y)).pull (fun _ => g * (g * g) * lam) (fun _ => stC g g false lam)
      (gridCl eightF [] g g false 0 lam y (gridR g g false lam Rm)) := rfl
end Eight.Level
