-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_hilbert_coefficient_eq_bounded_of_insert_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/aea17679-84b2-489c-8d0c-674a9b365623

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_insert_of_lt
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_insert_recurrence

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
    (k e : ℕ) (restricted : Finset (Fin k)) (j : Fin k)
    (hj : j ∉ restricted) (Hprev Hnext : ℕ → ℕ)
    (hprev : ∀ n, Hprev n =
      homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e n restricted)
    (hlow : ∀ n, n < e → Hnext n = Hprev n)
    (hrec : ∀ n, Hnext (e + n) + Hprev n = Hprev (e + n)) :
    ∀ n, Hnext n =
      homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e n
        (insert j restricted) := by
  intro n
  by_cases hn : n < e
  · calc
      Hnext n = Hprev n := hlow n hn
      _ = homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e n
        restricted := hprev n
      _ = homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e n
        (insert j restricted) :=
          (homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_insert_of_lt
            k e n restricted j hn).symm
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
    have hactual := hrec m
    have hbounded :=
      homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_insert_recurrence
        k e m restricted j hj
    have hprevlow := hprev m
    have hprevhigh := hprev (e + m)
    omega
end PermanentRollout
