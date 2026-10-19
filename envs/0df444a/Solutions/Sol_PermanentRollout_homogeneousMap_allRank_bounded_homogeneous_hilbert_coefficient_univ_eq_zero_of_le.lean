-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/4c713b8d-4064-4d78-aebe-3ffadc8a6fd8

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ

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
namespace PermanentRollout
theorem _root_.solution
    (k e n : ℕ) (hk : 0 < k) (hn : k * e ≤ n) :
    homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e n Finset.univ = 0 := by
  classical
  rw [homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ]
  unfold homogeneousMapAllKBoxHilbertCoefficient
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ ha
  have hstrict :
      (∑ i : Fin k, (a i : ℕ)) < ∑ _i : Fin k, e := by
    apply Finset.sum_lt_sum
    · intro i _
      exact Nat.le_of_lt (a i).isLt
    · refine ⟨⟨0, hk⟩, Finset.mem_univ _, ?_⟩
      exact (a ⟨0, hk⟩).isLt
  have hlt : (∑ i : Fin k, (a i : ℕ)) < k * e := by
    simpa using hstrict
  omega
end PermanentRollout
