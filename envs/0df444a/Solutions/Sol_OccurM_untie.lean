-- Prove2me | solution 1 for OccurM.untie
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:23:22.511056+00:00
-- url     : https://prove2.me/submissions/acebf9b1-b499-40ca-900d-35f2f561866c

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
import Theorems.Thm_ClausesOccur_boundInClausesIsHalf
import Theorems.Thm_P2M_GeneralPieces_x_Of_ge_2a558e3f9765
import Theorems.Thm_P2M_GeneralPieces_x_Of_pow_e8c07e605600


set_option autoImplicit false
section
section
open OccurM
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur
namespace OccurM
theorem _root_.solution : UntieStmt := by
  refine ⟨fun h => ⟨fun ρ c hE => ?_, fun ρ c hE => ?_⟩, fun h => ?_⟩
  · obtain ⟨P, A, val, hP⟩ := hE
    obtain ⟨M, -, C, hfin, -, hM⟩ := (h ρ c (GeneralPieces.x₀Of c) P A val hP (GeneralPieces.x₀Of_ge c) (GeneralPieces.x₀Of_pow c)).1.machine
    exact ⟨M, C, hfin, hM⟩
  · obtain ⟨P, A, val, hP⟩ := hE
    obtain ⟨M, -, C, hfin, -, hM⟩ := (h ρ c (GeneralPieces.x₀Of c) P A val hP (GeneralPieces.x₀Of_ge c) (GeneralPieces.x₀Of_pow c)).2.machine
    exact ⟨M, C, hfin, hM⟩
  · obtain ⟨c, P, A, val, -, t, -⟩ := h
    obtain ⟨M, -, C, hfin, -, hM⟩ := t.machine
    exact ⟨M, C, hfin, (boundInClausesIsHalf M C).2 hM⟩
end OccurM
