-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ_sum_of_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/9fdbea69-19d1-4e5b-bba4-c66f9591351c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ_sum
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ_eq_zero_of_le

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
    (k e N : ℕ) (hk : 0 < k) (hN : k * e ≤ N) :
    (∑ n ∈ Finset.range N,
      homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e n Finset.univ) =
        e ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Finset.sum_range_add]
  have htail :
      (∑ i ∈ Finset.range m,
        homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e
          (k * e + i) Finset.univ) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ_eq_zero_of_le
      k e (k * e + i) hk
    omega
  rw [htail, add_zero]
  exact homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ_sum k e hk
end PermanentRollout
