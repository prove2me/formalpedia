-- Prove2me | solution 1 for P2M_Eight_Level_Z__digOf_6fd272fe669a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:03.474865+00:00
-- url     : https://prove2.me/submissions/762aa136-ca3c-4d1b-bfaa-eacf7068424c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_Eight_Level_patOf_eq
import Theorems.Thm_Groundwork_Grid_ZG_congr
import Theorems.Thm_Paper_mem_rectangles


set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}
namespace Eight.Level
theorem _root_.solution (W : Inst (Fin g × Fin g) (Bits lam)) (y : ℕ) : Zι W (digOf g lam y) = Zι W (Eight.Level.patOf g lam y) :=
  ZG_congr _ fun q hq => by rw [patOf_eq g lam y hq]
end Eight.Level
