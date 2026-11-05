-- Prove2me | solution 1 for P2M_ClauseBound_Alg_GridNet_sum___rectIxG_27036c1cf533
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:15:38.450837+00:00
-- url     : https://prove2.me/submissions/1e4843f7-71e5-45bc-a936-0501bb0d35e9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_P2M_ClauseBound_Alg_GridNet_sum___ixG_ea3994ec108f
import Theorems.Thm_P2M_Groundwork_Grid_sum___swap_e6d8d32443c0


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (p d : ℕ) (tr : Bool) (f : ℕ → ℕ) :
    ∑ ω ∈ Ω (Fin (nParts p d tr)) (Fin (nMemb p d tr)), f (rectIxG d tr (tri ω.1.1 ω.1.2) (tri ω.2.1 ω.2.2)) =
      ∑ q ∈ range (nRectG p d), f q := by
  rw [← sum_Ω_ixG]
  cases tr
  · rfl
  · exact sum_Ω_swap (ρ := Fin p) (γ := Fin d) fun ω => f (ixG p d ω)
end ClauseBound.Alg.GridNet
