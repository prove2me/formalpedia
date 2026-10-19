-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_actualSourcePrefixHilbert_eq_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/a61a0b91-6cfb-42d9-8167-608fa9916bcd

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_empty
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_hilbert_coefficient_eq_bounded_of_insert_recurrence
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_sourcePrefix_succ
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_sourcePrefix_not_mem
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_sourcePrefix_isSMulRegular
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_actualCoordinateHilbert_empty
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_actualCoordinateHilbert_insert_of_lt
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_actualCoordinateHilbert_insert_recurrence_of_regular

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
namespace PermanentRollout
theorem _root_.solution
    (k : ℕ)
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (j : ℕ) (hj : j ≤ k) (n : ℕ) :
    homogeneousMapAllKActualCoordinateHilbert F (homogeneousMapAllKSourcePrefix k j) n =
      homogeneousMapAllKBoundedHomogeneousHilbertCoefficient
        k e n (homogeneousMapAllKSourcePrefix k j) := by
  induction j generalizing n with
  | zero =>
      rw [homogeneousMap_allRank_sourcePrefix_zero,
        homogeneousMap_allRank_actualCoordinateHilbert_empty,
        homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_empty]
  | succ j ih =>
      have hjlt : j < k := by omega
      let i : Fin k := ⟨j, hjlt⟩
      have hprev : ∀ m,
          homogeneousMapAllKActualCoordinateHilbert F
            (homogeneousMapAllKSourcePrefix k j) m =
          homogeneousMapAllKBoundedHomogeneousHilbertCoefficient
            k e m (homogeneousMapAllKSourcePrefix k j) := by
        intro m
        exact ih (by omega) m
      have hreg : IsSMulRegular
          (MvPolynomial (Fin k) ℂ ⧸
            homogeneousMapAllKCoordinateSubsetIdeal F (homogeneousMapAllKSourcePrefix k j))
          (F i) := by
        change IsSMulRegular
          (MvPolynomial (Fin k) ℂ ⧸
            Ideal.span (F ''
              (homogeneousMapAllKSourcePrefix k j : Set (Fin k))))
          (F ⟨j, hjlt⟩)
        exact homogeneousMap_allRank_sourcePrefix_isSMulRegular
          k F e he hF hzero j hjlt
      have hnext :=
        homogeneousMap_allRank_hilbert_coefficient_eq_bounded_of_insert_recurrence
          k e (homogeneousMapAllKSourcePrefix k j) i
          (homogeneousMap_allRank_sourcePrefix_not_mem hjlt)
          (homogeneousMapAllKActualCoordinateHilbert F
            (homogeneousMapAllKSourcePrefix k j))
          (homogeneousMapAllKActualCoordinateHilbert F
            (insert i (homogeneousMapAllKSourcePrefix k j))) hprev
          (fun m hm => homogeneousMap_allRank_actualCoordinateHilbert_insert_of_lt
            F hF (homogeneousMapAllKSourcePrefix k j) i m hm)
          (fun m =>
            homogeneousMap_allRank_actualCoordinateHilbert_insert_recurrence_of_regular
              F hF (homogeneousMapAllKSourcePrefix k j) i hreg m)
      rw [homogeneousMap_allRank_sourcePrefix_succ hjlt]
      exact hnext n
end PermanentRollout
