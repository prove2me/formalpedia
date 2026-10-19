-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_homogeneous_aeval_isSMulRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/3831a665-ffbe-43b7-a4f8-ef210a6d88c5

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_homogeneous_linear_sub_constant_isSMulRegular

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
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*}
    (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ))
    (t : MvPolynomial ι ℂ)
    (ht : t.IsHomogeneous 1)
    (htregular : IsSMulRegular (MvPolynomial ι ℂ ⧸ I) t)
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    IsSMulRegular (MvPolynomial ι ℂ ⧸ I)
      (Polynomial.aeval t p) := by
  classical
  have hleading : p.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hp
  have hunit : IsUnit
      (MvPolynomial.C p.leadingCoeff : MvPolynomial ι ℂ) :=
    (isUnit_iff_ne_zero.mpr hleading).map
      (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)
  have hregularLeading :
      IsSMulRegular (MvPolynomial ι ℂ ⧸ I)
        (MvPolynomial.C p.leadingCoeff) :=
    hunit.isSMulRegular _
  have hprod : ∀ roots : Multiset ℂ,
      IsSMulRegular (MvPolynomial ι ℂ ⧸ I)
        ((roots.map fun a => t - MvPolynomial.C a).prod) := by
    intro roots
    induction roots using Multiset.induction_on with
    | empty =>
        simp
    | @cons a roots ih =>
        simpa using
          (homogeneousMap_allTarget_homogeneous_linear_sub_constant_isSMulRegular
            I hI t ht htregular a).mul ih
  have hsplit := (IsAlgClosed.splits p).eq_prod_roots
  have heval := congrArg (Polynomial.aeval t) hsplit
  have heval' :
      Polynomial.aeval t p =
        MvPolynomial.C p.leadingCoeff *
          ((p.roots.map fun a => t - MvPolynomial.C a).prod) := by
    simpa [map_multiset_prod] using heval
  rw [heval']
  exact hregularLeading.mul (hprod p.roots)
end PermanentRollout
