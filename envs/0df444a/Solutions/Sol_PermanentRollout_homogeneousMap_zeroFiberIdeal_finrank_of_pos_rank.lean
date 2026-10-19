-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_zeroFiberIdeal_finrank_of_pos_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/c947a9cc-a346-4237-9d6f-d6ca8137b847

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_exists_high_homogeneousSubmodule_le_homogeneousMapIdeal
import Theorems.Thm_PermanentRollout_homogeneousMapIdeal_isHomogeneous
import Theorems.Thm_PermanentRollout_homogeneousMapFiniteGradedQuotient_finrank_eq_sum
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ_sum_of_cutoff
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_coordinateSubsetIdeal_univ
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_actualSourcePrefixHilbert_eq_bounded

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
    (k : ℕ) (hk : 0 < k)
    (F : Fin k → MvPolynomial (Fin k) ℂ)
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0) :
    Module.finrank ℂ
      (MvPolynomial (Fin k) ℂ ⧸ homogeneousMapIdeal F) = e ^ k := by
  classical
  obtain ⟨N₀, hN₀⟩ :=
    exists_high_homogeneousSubmodule_le_homogeneousMapIdeal F hzero
  let N : ℕ := max N₀ (k * e)
  have hhigh : ∀ n : ℕ, N ≤ n →
      ∀ p : MvPolynomial (Fin k) ℂ,
        p.IsHomogeneous n → p ∈ homogeneousMapIdeal F := by
    intro n hn p hp
    exact hN₀ n (le_trans (Nat.le_max_left _ _) hn) p hp
  calc
    Module.finrank ℂ
        (MvPolynomial (Fin k) ℂ ⧸ homogeneousMapIdeal F) =
      ∑ i : Fin N,
        Module.finrank ℂ
          (homogeneousMapGradedQuotientPiece (homogeneousMapIdeal F) i) :=
      homogeneousMapFiniteGradedQuotient_finrank_eq_sum
        (homogeneousMapIdeal F)
        (homogeneousMapIdeal_isHomogeneous F e hF) N hhigh
    _ = ∑ i : Fin N,
        homogeneousMapAllKBoundedHomogeneousHilbertCoefficient
          k e i Finset.univ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← homogeneousMap_allRank_coordinateSubsetIdeal_univ F,
        ← homogeneousMap_allRank_sourcePrefix_full k]
      exact homogeneousMap_allRank_actualSourcePrefixHilbert_eq_bounded
        k F e he hF hzero k (le_refl k) i
    _ = ∑ n ∈ Finset.range N,
        homogeneousMapAllKBoundedHomogeneousHilbertCoefficient
          k e n Finset.univ :=
      Fin.sum_univ_eq_sum_range
        (fun n => homogeneousMapAllKBoundedHomogeneousHilbertCoefficient
          k e n Finset.univ) N
    _ = e ^ k :=
      homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ_sum_of_cutoff
        k e N hk (Nat.le_max_right _ _)
end PermanentRollout
