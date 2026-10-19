-- Prove2me | solution 1 for PermanentRollout.floor_sourceTreeSeparatedMinorSum_eq_sourceSeparatedBlockMinorSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/035a0268-f81f-4d8c-ba47-b5e1a1627f30

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_flattened_sourceTreeSeparatedMinorSum_eq_flattenedSeparatedBlockMinorSum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    (n d : ℕ) (tree : BlockTree (Fin (blockCount n d))) :
    MvPolynomial.rename
        (finProdFinEquiv :
          Fin (blockRows n d) × Fin (blockColumns n d) ≃
            Fin (blockVariables n d))
        (sourceTreeSeparatedMinorSum
          (blockCount n d) (blockWidth d) (blockColumns n d) d tree) =
      sourceSeparatedBlockMinorSum n d
        (sourceTreeBlockWeight (blockCount n d) d tree) := by
  exact flattened_sourceTreeSeparatedMinorSum_eq_flattenedSeparatedBlockMinorSum
    (blockCount n d) (blockWidth d) (blockColumns n d) d tree
end PermanentRollout
