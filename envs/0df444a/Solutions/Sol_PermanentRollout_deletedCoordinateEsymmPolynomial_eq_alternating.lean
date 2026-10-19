-- Prove2me | solution 1 for PermanentRollout.deletedCoordinateEsymmPolynomial_eq_alternating
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/a555cc8a-e7c4-421b-a42e-84e5ee761387

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_partitionFiberCoordinateEsymmPolynomial_succ_eq_deleted

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    (t : ℕ) (i : Fin t) (q : ℕ) :
    deletedCoordinateEsymmPolynomial t q i =
      ∑ j ∈ Finset.range (q + 1),
        (-MvPolynomial.X i) ^ (q - j) *
          partitionFiberCoordinateEsymmPolynomial t j := by
  classical
  induction q with
  | zero =>
      simp [deletedCoordinateEsymmPolynomial,
        partitionFiberCoordinateEsymmPolynomial,
        MvPolynomial.esymm, Multiset.esymm]
  | succ q ih =>
      have hrec :=
        partitionFiberCoordinateEsymmPolynomial_succ_eq_deleted t q i
      have hdeleted :
          deletedCoordinateEsymmPolynomial t (q + 1) i =
            partitionFiberCoordinateEsymmPolynomial t (q + 1) -
              MvPolynomial.X i * deletedCoordinateEsymmPolynomial t q i := by
        linear_combination -hrec
      have hsum :
          (∑ j ∈ Finset.range (q + 1),
            (-MvPolynomial.X i) ^ (q + 1 - j) *
              partitionFiberCoordinateEsymmPolynomial t j) =
            -(MvPolynomial.X i *
              ∑ j ∈ Finset.range (q + 1),
                (-MvPolynomial.X i) ^ (q - j) *
                  partitionFiberCoordinateEsymmPolynomial t j) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hjle : j ≤ q := by
          have hjrange := Finset.mem_range.mp hj
          omega
        rw [show q + 1 - j = (q - j) + 1 by omega, pow_succ]
        ring
      have hfinal :
          (∑ j ∈ Finset.range (q + 1 + 1),
            (-MvPolynomial.X i) ^ (q + 1 - j) *
              partitionFiberCoordinateEsymmPolynomial t j) =
            (∑ j ∈ Finset.range (q + 1),
              (-MvPolynomial.X i) ^ (q + 1 - j) *
                partitionFiberCoordinateEsymmPolynomial t j) +
              partitionFiberCoordinateEsymmPolynomial t (q + 1) := by
        rw [Finset.sum_range_succ]
        simp
      calc
        deletedCoordinateEsymmPolynomial t (q + 1) i =
            partitionFiberCoordinateEsymmPolynomial t (q + 1) -
              MvPolynomial.X i * deletedCoordinateEsymmPolynomial t q i :=
          hdeleted
        _ = partitionFiberCoordinateEsymmPolynomial t (q + 1) -
              MvPolynomial.X i *
                ∑ j ∈ Finset.range (q + 1),
                  (-MvPolynomial.X i) ^ (q - j) *
                    partitionFiberCoordinateEsymmPolynomial t j := by
          rw [ih]
        _ = ∑ j ∈ Finset.range (q + 1 + 1),
              (-MvPolynomial.X i) ^ (q + 1 - j) *
                partitionFiberCoordinateEsymmPolynomial t j := by
          rw [hfinal, hsum]
          ring
end PermanentRollout
