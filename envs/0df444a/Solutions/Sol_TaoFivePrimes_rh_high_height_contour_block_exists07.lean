-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_contour_block_exists07
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T14:56:53.478827+00:00
-- url     : https://prove2.me/submissions/2461beac-0890-4edc-9d4f-db678cc4f831

import Definitions.Def_TaoFivePrimes_RHHighContourBlocks
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_subblock_exists07_0
import Theorems.Thm_TaoFivePrimes_rh_high_height_contour_subblock_exists07_1
theorem solution : Nonempty (RHHighContourBlocks.Block 7168 1024 (109375781341265174060677403094527124681626:Int)) := by
 rcases TaoFivePrimes.rh_high_height_contour_subblock_exists07_0 with ⟨a⟩
 rcases TaoFivePrimes.rh_high_height_contour_subblock_exists07_1 with ⟨b⟩
 exact ⟨RHHighContourBlocks.append a b⟩
#print axioms solution
