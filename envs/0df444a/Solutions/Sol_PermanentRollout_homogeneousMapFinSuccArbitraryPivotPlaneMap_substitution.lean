-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFinSuccArbitraryPivotPlaneMap_substitution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/fba02159-6cf6-4a63-a760-6c5927053a03

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMapFinSuccFirstPivotPlaneMap_substitution
import Theorems.Thm_PermanentRollout_homogeneousMapFinSuccArbitraryPivotPlaneMap_coordinate

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
    (j : Fin (n + 1))
    (p : MvPolynomial (Fin (n + 1)) ℂ) :
    (MvPolynomial.finSuccEquiv ℂ n
      (MvPolynomial.rename (Equiv.swap (0 : Fin (n + 1)) j) p)).eval
        (homogeneousMapFinSuccFirstPivotPlaneRoot
          (fun i => c ((Equiv.swap (0 : Fin (n + 1)) j).symm i))) =
      MvPolynomial.aeval
        (fun row => linearCoordinatePolynomial
          (homogeneousMapFinSuccArbitraryPivotPlaneMap c j) row) p := by
  rw [homogeneousMapFinSuccFirstPivotPlaneMap_substitution,
    MvPolynomial.aeval_rename]
  apply congrArg
    (fun coordinates : Fin (n + 1) → MvPolynomial (Fin n) ℂ =>
      MvPolynomial.aeval coordinates p)
  funext i
  exact (homogeneousMapFinSuccArbitraryPivotPlaneMap_coordinate c j i).symm
end PermanentRollout
