-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_reesCoordinate_quotient_isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/26999637-cb6e-4522-9e1b-7d1479803508

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_ringEquiv_isWeaklyRegular_ofFn_image
import Theorems.Thm_PermanentRollout_homogeneousMap_coordinatePolynomials_isWeaklyRegular
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_reesZeroHyperplaneEquiv_coordinate

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
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
open scoped BigOperators
open scoped Pointwise
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Pointwise BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    RingTheory.Sequence.IsWeaklyRegular
      (MvPolynomial (Fin (k + 1)) ℂ ⧸
        Ideal.span ({MvPolynomial.X (0 : Fin (k + 1))} :
          Set (MvPolynomial (Fin (k + 1)) ℂ)))
      (List.ofFn fun i : Fin k =>
        Ideal.Quotient.mk
          (Ideal.span ({MvPolynomial.X (0 : Fin (k + 1))} :
            Set (MvPolynomial (Fin (k + 1)) ℂ)))
          (homogeneousMapAllTargetReesCoordinate F target e i)) := by
  have hsource :=
    homogeneousMap_coordinatePolynomials_isWeaklyRegular
      k F e he hF hzero
  have hcoord (i : Fin k) :
      (homogeneousMapAllTargetReesZeroHyperplaneEquiv k).toRingEquiv
        (Ideal.Quotient.mk
          (Ideal.span ({MvPolynomial.X (0 : Fin (k + 1))} :
            Set (MvPolynomial (Fin (k + 1)) ℂ)))
          (homogeneousMapAllTargetReesCoordinate F target e i)) = F i :=
    homogeneousMap_allTarget_reesZeroHyperplaneEquiv_coordinate F target e he i
  apply homogeneousMap_allRank_ringEquiv_isWeaklyRegular_ofFn_image
    (homogeneousMapAllTargetReesZeroHyperplaneEquiv k).toRingEquiv
    (fun i : Fin k =>
      Ideal.Quotient.mk
        (Ideal.span ({MvPolynomial.X (0 : Fin (k + 1))} :
          Set (MvPolynomial (Fin (k + 1)) ℂ)))
        (homogeneousMapAllTargetReesCoordinate F target e i))
  simpa only [hcoord] using hsource
end PermanentRollout
