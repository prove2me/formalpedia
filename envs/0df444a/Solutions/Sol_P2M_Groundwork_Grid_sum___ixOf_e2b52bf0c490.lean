-- Prove2me | solution 1 for P2M_Groundwork_Grid_sum___ixOf_e2b52bf0c490
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:10:00.860458+00:00
-- url     : https://prove2.me/submissions/84c19f46-2e3e-4606-9204-51be178717e3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_Digits
import Theorems.Thm_Groundwork_Grid_ixOf_bijOn

set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect)
namespace Groundwork.Grid
theorem _root_.solution (g : ℕ) (f : ℕ → ℕ) : ∑ ω ∈ Ω (Fin g) (Fin g), f (ixOf g ω) = ∑ q ∈ range (nRect g), f q := by
  exact Finset.sum_nbij (ixOf g) (fun ω hω => Finset.mem_coe.1 ((ixOf_bijOn g).mapsTo (Finset.mem_coe.2 hω)))
    (ixOf_bijOn g).injOn (ixOf_bijOn g).surjOn fun _ _ => rfl
end Groundwork.Grid
