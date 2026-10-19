-- Prove2me | solution 1 for PermanentRollout.sourceSeparatedBlockMinorSum_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/1b1db48f-48f6-4e64-9679-78eb8882069f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_flattenedSeparatedBlockMinorSum_isHomogeneous

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    (n d : ℕ) (weight : Fin (blockCount n d) → ℂ) :
    (sourceSeparatedBlockMinorSum n d weight).IsHomogeneous d := by
  exact flattenedSeparatedBlockMinorSum_isHomogeneous
    (blockCount n d) (blockWidth d) (blockColumns n d) d weight
end PermanentRollout
