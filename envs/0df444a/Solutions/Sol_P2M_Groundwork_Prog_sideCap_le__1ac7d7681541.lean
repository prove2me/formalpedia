-- Prove2me | solution 1 for P2M_Groundwork_Prog_sideCap_le__1ac7d7681541
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:44:06.598708+00:00
-- url     : https://prove2.me/submissions/dff4c507-38ad-40cf-acd6-d7368085a037

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Cut
import Definitions.Def_ToTuring_Poly_Grid
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ToTuring_Poly_GridSide
import Theorems.Thm_Groundwork_Grid_rectLen_le
import Theorems.Thm_Groundwork_Grid_sideCnt_rectDig_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Stepped
open Groundwork.Grid (sideCnt he node c2 rectIx rectDig rectLen sideChunk sideCap sideCnt_rectDig_le rectLen_le)
variable {α : Type} [Enc α] (g : ℕ) (tr : Bool)
namespace Groundwork.Prog
theorem _root_.solution (n y a b : ℕ) : sideCap g tr n y a b ≤ g * n + c2 g * (3 * n + 1) := by
  unfold sideCap
  refine Nat.add_le_add_left ((Finset.sum_le_card_nsmul _ _ _ fun κ _ => rectLen_le g tr n y _ κ).trans ?_) _
  rw [Finset.card_range, smul_eq_mul]
end Groundwork.Prog
