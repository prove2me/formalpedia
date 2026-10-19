-- Prove2me | solution 1 for PermanentRollout.sourceTreeSeparatedMinorSum_eq_separatedBlockMinorSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/2e03dfe5-6d7b-4b17-9456-77773d98ab69

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    (b t s d : ℕ) (tree : BlockTree (Fin b)) :
    sourceTreeSeparatedMinorSum b t s d tree =
      separatedBlockMinorSum b t s d
        (sourceTreeBlockWeight b d tree) := by
  rfl
end PermanentRollout
