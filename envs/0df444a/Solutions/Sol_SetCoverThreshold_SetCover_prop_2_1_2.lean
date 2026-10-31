-- Prove2me | solution 1 for SetCoverThreshold.SetCover.prop_2_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T19:47:08.344792+00:00
-- url     : https://prove2.me/submissions/918407dd-59af-4778-8f1b-3d9eafda9d61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Theorems.Thm_SetCoverThreshold_SetCover_gapNPHard_of_reduction
import Theorems.Thm_SetCoverThreshold_SetCover_exists_formula5_reduction

set_option autoImplicit false
set_option linter.unusedVariables false

open SetCoverThreshold.SetCover

theorem solution (h211 : Thm211) :
    ∃ ε : ℝ, 0 < ε ∧
      GapNPHard (fun φ : Formula5 => CookPvsNP.encodeCNF φ.toCNF)
        (fun φ => φ.toCNF.Satisfiable) (fun φ => AtMostFracSat (1 - ε) φ.toCNF) := by
  obtain ⟨B, ε₀, hε₀, hgap⟩ := h211
  obtain ⟨ε, g, g_enc, hε, hg_poly, hg_enc, hg_yes, hg_no⟩ :=
    exists_formula5_reduction B ε₀ hε₀
  refine ⟨ε, hε, ?_⟩
  exact gapNPHard_of_reduction
    CookPvsNP.encodeCNF
    (fun F => Is3CNFB B F ∧ F.Satisfiable)
    (fun F => Is3CNFB B F ∧ AtMostFracSat (1 - ε₀) F)
    (fun φ : Formula5 => CookPvsNP.encodeCNF φ.toCNF)
    (fun φ => φ.toCNF.Satisfiable)
    (fun φ => AtMostFracSat (1 - ε) φ.toCNF)
    hgap g g_enc hg_poly hg_enc hg_yes hg_no
