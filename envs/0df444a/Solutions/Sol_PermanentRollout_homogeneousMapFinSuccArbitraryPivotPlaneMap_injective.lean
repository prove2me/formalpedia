-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFinSuccArbitraryPivotPlaneMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/e83d636e-4469-439d-ac2d-51d0f138d25d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMapFinSuccFirstPivotPlaneMap_injective

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
    {n : ℕ} (c : Fin (n + 1) → ℂ) (j : Fin (n + 1)) :
    Function.Injective (homogeneousMapFinSuccArbitraryPivotPlaneMap c j) := by
  intro u v huv
  apply homogeneousMapFinSuccFirstPivotPlaneMap_injective
    (fun i => c ((Equiv.swap (0 : Fin (n + 1)) j).symm i))
  funext i
  have hi := congrFun huv
    ((Equiv.swap (0 : Fin (n + 1)) j).symm i)
  simpa [homogeneousMapFinSuccArbitraryPivotPlaneMap,
    homogeneousMapFinSuccPivotPermutation] using hi
end PermanentRollout
