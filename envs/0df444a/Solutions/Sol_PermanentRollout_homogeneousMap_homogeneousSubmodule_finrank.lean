-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_homogeneousSubmodule_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/fec9bdb5-dc31-40c4-ac0d-a47969d33bf3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_degreeSupport_eq_antidiagonal

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Fintype ι] (n : ℕ) :
    Module.finrank ℂ (MvPolynomial.homogeneousSubmodule ι ℂ n) =
      (Fintype.card ι + n - 1).choose n := by
  classical
  let a : Finset (ι →₀ ℕ) :=
    (Finset.univ : Finset ι).finsuppAntidiag n
  have ha : {d : ι →₀ ℕ | d.degree = n} =
      (a : Set (ι →₀ ℕ)) :=
    homogeneousMap_degreeSupport_eq_antidiagonal n
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported, ha]
  change Module.finrank ℂ
    (MvPolynomial.restrictSupport ℂ (a : Set (ι →₀ ℕ))) =
      (Fintype.card ι + n - 1).choose n
  rw [Module.finrank_eq_card_finset_basis
    (MvPolynomial.basisRestrictSupport ℂ (a : Set (ι →₀ ℕ)))]
  exact Finset.card_finsuppAntidiag_nat_eq_choose n
end PermanentRollout
