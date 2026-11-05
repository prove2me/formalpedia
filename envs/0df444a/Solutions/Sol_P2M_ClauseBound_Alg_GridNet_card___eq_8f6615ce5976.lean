-- Prove2me | solution 1 for P2M_ClauseBound_Alg_GridNet_card___eq_8f6615ce5976
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:07:36.404378+00:00
-- url     : https://prove2.me/submissions/f560518d-9d5f-4bba-9e31-a4af4e9882fa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_P2M_ClauseBound_Grid_card___pd_ac2b31513cb7


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (p d : ℕ) : #(Ω (Fin p) (Fin d)) = nRectG p d := by
  rw [ClauseBound.Grid.card_Ω_pd (Fintype.card_fin p) (Fintype.card_fin d), Nat.choose_two_right, Nat.choose_two_right]
  rfl
end ClauseBound.Alg.GridNet
