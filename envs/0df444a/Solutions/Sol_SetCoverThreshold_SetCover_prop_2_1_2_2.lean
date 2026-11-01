-- Prove2me | solution 2 for SetCoverThreshold.SetCover.prop_2_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T11:57:58.187298+00:00
-- url     : https://prove2.me/submissions/33ab7042-7583-458d-ba5f-7dce4235f121
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Theorems.Thm_SetCoverThreshold_SetCover_exists_formula5_reduction
import Theorems.Thm_SetCoverThreshold_SetCover_gapNPHard_of_reduction

open SetCoverThreshold.SetCover

theorem solution (h211 : Thm211) :
    ∃ ε : ℝ, 0 < ε ∧
      GapNPHard (fun φ : Formula5 => CookPvsNP.encodeCNF φ.toCNF)
        (fun φ => φ.toCNF.Satisfiable) (fun φ => AtMostFracSat (1 - ε) φ.toCNF) := by
  rcases h211 with ⟨B, ε₀, hε₀, hHard⟩
  rcases exists_formula5_reduction B ε₀ hε₀ with ⟨ε, g, g_enc, hε, hg_poly, hg_enc, hg_yes, hg_no⟩
  exact ⟨ε, hε, gapNPHard_of_reduction _ _ _ _ _ _ hHard g g_enc hg_poly hg_enc hg_yes hg_no⟩
