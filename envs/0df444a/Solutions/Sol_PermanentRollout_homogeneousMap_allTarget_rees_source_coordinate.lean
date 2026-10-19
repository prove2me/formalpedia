-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_rees_source_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/eacdd6ba-5726-4636-8bc5-19be90a4e74d

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
    (target : Fin k → ℂ) (e : ℕ) (i : Fin k) :
    homogeneousMapAllTargetReesSourceRingHom F target e
      (⟨F i, homogeneousMap_coordinate_mem_subalgebra F i⟩ :
        homogeneousMapSubalgebra F) =
      homogeneousMapAllTargetReesParameterRingHom F target e
        (Polynomial.C (target i) * Polynomial.X ^ e) := by
  let I := Ideal.span (Set.range
    (homogeneousMapAllTargetReesCoordinate F target e))
  have hmem : homogeneousMapAllTargetReesCoordinate F target e i ∈ I :=
    Ideal.subset_span ⟨i, rfl⟩
  have hzero : Ideal.Quotient.mk I
      (homogeneousMapAllTargetReesCoordinate F target e i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  change Ideal.Quotient.mk I (MvPolynomial.rename Fin.succ (F i)) =
    Ideal.Quotient.mk I
      ((Polynomial.aeval
        (MvPolynomial.X (R := ℂ) (0 : Fin (k + 1))))
        (Polynomial.C (target i) * Polynomial.X ^ e))
  rw [map_mul, map_pow, Polynomial.aeval_X]
  have hC : (Polynomial.aeval
      (MvPolynomial.X (R := ℂ) (0 : Fin (k + 1))))
      (Polynomial.C (target i)) = MvPolynomial.C (target i) := by
    simp
  rw [hC]
  apply sub_eq_zero.mp
  simpa [homogeneousMapAllTargetReesCoordinate, map_sub] using hzero
end PermanentRollout
