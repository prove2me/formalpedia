-- Prove2me | solution 1 for actuarial_f_survivor_replacement_respects_floor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:55:52.507554+00:00
-- url     : https://prove2.me/submissions/3d53bf0a-b5cb-4c9b-87e7-d79f5aa5d3aa

import Mathlib
import Definitions.Def_actuarial_f_gmpProtectedSurvivorReplacement
open ActuarialUnderpinsF

theorem solution
    (replace : Prop) (scheme statutory : ℝ) :
    statutory ≤ gmpProtectedSurvivorReplacement replace scheme statutory := by
  unfold gmpProtectedSurvivorReplacement gmpProtectedSurvivorParallel
  split_ifs
  · exact le_refl _
  · exact le_max_right _ _
