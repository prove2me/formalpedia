-- Prove2me | solution 1 for SuspensionContract.ControlBand.proposition_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:32:23.591997+00:00
-- url     : https://prove2.me/submissions/fc9ecdc4-9697-422f-a5ad-b4a76c70e471
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SuspensionContract_ControlBand_Thresholds
import Definitions.Def_SuspensionContract_ControlBand_Construction
import Theorems.Thm_SuspensionContract_ControlBand_EC3_9_construction

open SuspensionContract.ControlBand

theorem solution (P : Params) (hP : P.Standing) (h3 : P.Condition3) :
    ∃ c wB thHi thLo : ℝ, P.Prop6Params c wB thHi thLo := by
  obtain ⟨th, -, -, h6⟩ := EC3_9_construction P hP h3
  exact ⟨_, _, _, _, h6⟩
