-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.cokernelLowerBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:30:31.063892+00:00
-- url     : https://prove2.me/submissions/c285e88a-434b-4574-aaa8-14beae360767

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Theorems.Thm_ReciprocityTheory_PGsh_Up_permutedCokernelLowerBound_of
import Theorems.Thm_ReciprocityTheory_PGsh_Up_unramifiedCokernelLowerBound_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hU6 : CokernelLengthComparisonStatement) (hU7 : UnramifiedCokernelLengthStatement) (hEx : LenExStatement)
    (hKG : KilledGenStatement) (hIG : IdemGenStatement) : CokernelLowerBoundStatement := by
  exact And.intro (permutedCokernelLowerBound_of hU6 hEx hKG hIG) (unramifiedCokernelLowerBound_of hU7 hEx hKG hIG)
end ReciprocityTheory.PGsh.Up
