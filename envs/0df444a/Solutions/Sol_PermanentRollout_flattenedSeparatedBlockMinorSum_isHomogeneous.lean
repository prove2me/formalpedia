-- Prove2me | solution 1 for PermanentRollout.flattenedSeparatedBlockMinorSum_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/658b2508-4855-4f84-a7b3-ba2d76b5305c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_separatedBlockMinorSum_isHomogeneous

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    (b t s d : ℕ) (weight : Fin b → ℂ) :
    (flattenedSeparatedBlockMinorSum b t s d weight).IsHomogeneous d := by
  exact MvPolynomial.IsHomogeneous.rename_isHomogeneous
    (separatedBlockMinorSum_isHomogeneous b t s d weight)
end PermanentRollout
