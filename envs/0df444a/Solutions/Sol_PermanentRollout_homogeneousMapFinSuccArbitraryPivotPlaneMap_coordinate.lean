-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFinSuccArbitraryPivotPlaneMap_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/ac4ac86d-6338-4972-8923-491493670b93

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {n : ℕ} (c : Fin (n + 1) → ℂ)
    (j i : Fin (n + 1)) :
    linearCoordinatePolynomial
      (homogeneousMapFinSuccArbitraryPivotPlaneMap c j) i =
    linearCoordinatePolynomial
      (homogeneousMapFinSuccFirstPivotPlaneMap
        (fun q => c ((Equiv.swap (0 : Fin (n + 1)) j).symm q)))
      (Equiv.swap (0 : Fin (n + 1)) j i) := by
  simp [linearCoordinatePolynomial,
    homogeneousMapFinSuccArbitraryPivotPlaneMap,
    homogeneousMapFinSuccPivotPermutation]
end PermanentRollout
