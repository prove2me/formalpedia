-- Prove2me | solution 1 for Paper.card_rectangles_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:16:55.963788+00:00
-- url     : https://prove2.me/submissions/409cb46d-ace7-4b24-9834-ad66ecc8ed5e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_DefFactor
import Definitions.Def_Paper_SecCrossing_Crossing
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_Paper_SecLevel_Grid
import Theorems.Thm_P2M_Groundwork_Grid_four_mul_card___le_d3f46a4334e3


set_option autoImplicit false
section
section
open Paper
open Finset Groundwork
variable {g lam : ℕ}
namespace Paper
theorem _root_.solution (g : ℕ) : (#(rectangles g) : ℝ) ≤ (g : ℝ) ^ 4 / 4 := by
  have h : 4 * #(rectangles g) ≤ g ^ 4 := Grid.four_mul_card_Ω_le (Fintype.card_fin g) (Fintype.card_fin g)
  have h' : 4 * (#(rectangles g) : ℝ) ≤ (g : ℝ) ^ 4 := by exact_mod_cast h
  linarith
end Paper
