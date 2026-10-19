-- Prove2me | solution 1 for PermanentRollout.flattened_sourceTreeSeparatedMinorSum_eq_flattenedSeparatedBlockMinorSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/d9904882-1831-4a9d-9eea-06e9c48321d1

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_sourceTreeSeparatedMinorSum_eq_separatedBlockMinorSum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    (b t s d : ℕ) (tree : BlockTree (Fin b)) :
    MvPolynomial.rename
        (finProdFinEquiv :
          Fin (b * t) × Fin s ≃ Fin ((b * t) * s))
        (sourceTreeSeparatedMinorSum b t s d tree) =
      flattenedSeparatedBlockMinorSum b t s d
        (sourceTreeBlockWeight b d tree) := by
  unfold flattenedSeparatedBlockMinorSum
  rw [sourceTreeSeparatedMinorSum_eq_separatedBlockMinorSum]
end PermanentRollout
