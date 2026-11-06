-- Prove2me | solution 1 for OccurM.boundInClausesTied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:37:30.868605+00:00
-- url     : https://prove2.me/submissions/3f76975c-ea95-4248-b4c8-90ad8605e9b3

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
import Theorems.Thm_AppRunningTime_thmHalfPieces
import Theorems.Thm_GeneralPieces_Asymptotic_alpha_half
import Theorems.Thm_GeneralPieces_boundInM_tied
import Theorems.Thm_GeneralPieces_thmHalfPieces
import Theorems.Thm_OccurM_topOccurOfTop


set_option autoImplicit false
section
section
open OccurM
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur
namespace OccurM
theorem _root_.solution : BoundInClausesTied := by
  obtain ⟨c, P, A, val, hB, hC⟩ := GeneralPieces.boundInM_tied AppRunningTime.thmHalfPieces
  unfold GeneralPieces.Tied.PartCm AppRunningTime.alpha' at hC
  rw [GeneralPieces.Asymptotic.alpha_half] at hC
  obtain ⟨t1, t2⟩ := topOccurOfTop _ _ _ _ (by norm_num) (by norm_num) hC
  exact ⟨c, P, A, val, hB, t1, t2⟩
end OccurM
