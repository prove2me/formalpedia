-- Prove2me | solution 1 for P2M_ClauseBound_Alg_GridNet_sum___ixG_ea3994ec108f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:07:40.43232+00:00
-- url     : https://prove2.me/submissions/24121668-9fcb-4d68-b7ad-47e4159f442f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_ClauseBound_Alg_GridNet_ixG_bijOn

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
namespace ClauseBound.Alg.GridNet
theorem _root_.solution (p d : ℕ) (f : ℕ → ℕ) : ∑ ω ∈ Ω (Fin p) (Fin d), f (ixG p d ω) = ∑ q ∈ range (nRectG p d), f q :=
  Finset.sum_nbij (ixG p d) (fun _ hω => Finset.mem_coe.1 ((ixG_bijOn p d).mapsTo (Finset.mem_coe.2 hω)))
    (ixG_bijOn p d).injOn (ixG_bijOn p d).surjOn fun _ _ => rfl
end ClauseBound.Alg.GridNet
