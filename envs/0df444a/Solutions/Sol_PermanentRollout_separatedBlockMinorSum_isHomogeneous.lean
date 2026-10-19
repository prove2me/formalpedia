-- Prove2me | solution 1 for PermanentRollout.separatedBlockMinorSum_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/03b50a4f-0aa3-4f87-b6b7-bbff2247fd08

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_minorSum_isHomogeneous

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    (b t s d : ℕ) (weight : Fin b → ℂ) :
    (separatedBlockMinorSum b t s d weight).IsHomogeneous d := by
  classical
  unfold separatedBlockMinorSum
  apply MvPolynomial.IsHomogeneous.sum
  intro h _
  exact (minorSum_isHomogeneous t s d).rename_isHomogeneous.C_mul (weight h)
end PermanentRollout
