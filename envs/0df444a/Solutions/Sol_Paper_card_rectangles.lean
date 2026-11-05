-- Prove2me | solution 1 for Paper.card_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:09:00.335283+00:00
-- url     : https://prove2.me/submissions/1f525bae-36cf-4be3-96ff-f4035dc1aa1b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_DefFactor
import Definitions.Def_Paper_SecCrossing_Crossing
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Paper_SecLevel_Grid
import Theorems.Thm_P2M_Groundwork_Grid_card___1355cab52dbf


set_option autoImplicit false
section
section
open Paper
open Finset Groundwork
variable {g lam : ℕ}
namespace Paper
theorem _root_.solution (g : ℕ) : #(rectangles g) = g.choose 2 ^ 2 :=
  Grid.card_Ω (Fintype.card_fin g) (Fintype.card_fin g)
end Paper
