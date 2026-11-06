-- Prove2me | solution 1 for OccurM.countsFromPiecesTied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:31:33.052902+00:00
-- url     : https://prove2.me/submissions/18bf2393-0564-4798-88cc-e1fd7f064eab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_OccurM_Arith
import Definitions.Def_OccurM_Top
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_GeneralPieces_Num_PartD
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_OccurM_Main
import Theorems.Thm_ClauseBound_Gen_End_alpha_mem
import Theorems.Thm_GeneralPieces_PartD_alpha_mem
import Theorems.Thm_GeneralPieces_thmRunningTimeCm_tied
import Theorems.Thm_OccurM_topOccurOfTop
import Theorems.Thm_PaddedDescent_F_Price_rho_lt


set_option autoImplicit false
section
section
open OccurM
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur
namespace OccurM
theorem _root_.solution : CountsFromPiecesTied := fun ρ c x₀ P A val h hx hc =>
  topOccurOfTop _ _ _ _ (GeneralPieces.PartD.alpha_mem ρ h.rho_ge h.rho_lt).1 (GeneralPieces.PartD.alpha_mem ρ h.rho_ge h.rho_lt).2 (GeneralPieces.thmRunningTimeCm_tied ρ c x₀ P A val h hx hc)
end OccurM
