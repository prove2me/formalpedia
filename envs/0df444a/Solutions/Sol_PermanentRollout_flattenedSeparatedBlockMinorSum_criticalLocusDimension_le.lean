-- Prove2me | solution 1 for PermanentRollout.flattenedSeparatedBlockMinorSum_criticalLocusDimension_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/f260fa3d-bb5a-4293-8481-f31ea6f07ccc

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_blockIncidence_ringKrullDim_le_degree
import Theorems.Thm_PermanentRollout_flattenedSeparatedBlockMinorSum_criticalLocusDimension_le_of_incidence

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {b t s d : ℕ} (hd : 3 ≤ d) (ht : d ≤ t)
    (weight : Fin b → ℂ) (hw : ∀ h, weight h ≠ 0) :
    criticalLocusDimension
      (flattenedSeparatedBlockMinorSum b t s d weight) ≤
        ((b * ((2 ^ t - 1) + s * (d - 2)) : ℕ) : WithBot ℕ∞) := by
  exact flattenedSeparatedBlockMinorSum_criticalLocusDimension_le_of_incidence
    hd weight hw (blockIncidence_ringKrullDim_le_degree hd ht)
end PermanentRollout
