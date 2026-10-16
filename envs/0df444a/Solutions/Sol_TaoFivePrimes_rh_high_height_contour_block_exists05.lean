-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_contour_block_exists05
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T14:49:20.987229+00:00
-- url     : https://prove2.me/submissions/709742fd-59bb-4247-b3ae-404811f41d83

import Definitions.Def_TaoFivePrimes_RHHighContourBlocks
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_subblock_exists05_0
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_subblock_exists05_1
theorem solution : Nonempty (RHHighContourBlocks.Block 5120 1024 (109557364323034730827380755535190168203882:Int)) := by
 rcases TaoFivePrimes.rh_high_height_contour_subblock_exists05_0 with ⟨a⟩
 rcases TaoFivePrimes.rh_high_height_contour_subblock_exists05_1 with ⟨b⟩
 exact ⟨RHHighContourBlocks.append a b⟩
#print axioms solution
