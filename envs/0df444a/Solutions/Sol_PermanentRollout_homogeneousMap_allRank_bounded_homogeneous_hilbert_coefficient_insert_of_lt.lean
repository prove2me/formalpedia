-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_insert_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/e4252ecb-5d6f-4c43-9153-cb35de0f9694

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
namespace PermanentRollout
theorem _root_.solution
    (k e n : ℕ) (restricted : Finset (Fin k)) (j : Fin k)
    (hn : n < e) :
    homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e n
        (insert j restricted) =
      homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e n restricted := by
  classical
  unfold homogeneousMapAllKBoundedHomogeneousHilbertCoefficient
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag,
    Finset.subset_univ, and_true, Finset.mem_insert]
  constructor
  · rintro ⟨hd, h⟩
    exact ⟨hd, fun i hi => h i (Or.inr hi)⟩
  · rintro ⟨hd, _⟩
    refine ⟨hd, fun i _ => ?_⟩
    have hdegree : d.degree = n := by
      simpa [Finsupp.degree_eq_sum] using hd
    have hi := Finsupp.le_degree i d
    omega
end PermanentRollout
