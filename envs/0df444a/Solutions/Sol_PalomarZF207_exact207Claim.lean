-- Prove2me | solution 1 for PalomarZF207.exact207Claim
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:52:36.541135+00:00
-- url     : https://prove2.me/submissions/95aee6df-f3aa-4df4-af56-71b29f43c2c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_palomar_zf207_history
import Definitions.Def_palomar_zf207_zf
import Definitions.Def_palomar_zf207_statement
import Theorems.Thm_PalomarZF207_represents207_exists
import Theorems.Thm_PalomarZF207_neg_unprovable_of_represents207
import Theorems.Thm_PalomarZF207_halt_unprovable_of_sigma1_sound
import Theorems.Thm_PalomarZF207_sigma1_sound_consistent

open PalomarZF207

theorem solution : Exact207Claim := by
  obtain ⟨H, hH⟩ := represents207_exists
  exact ⟨H, hH, neg_unprovable_of_represents207 H hH, fun hs =>
    ⟨halt_unprovable_of_sigma1_sound H hH hs,
     neg_unprovable_of_represents207 H hH (sigma1_sound_consistent hs)⟩⟩
