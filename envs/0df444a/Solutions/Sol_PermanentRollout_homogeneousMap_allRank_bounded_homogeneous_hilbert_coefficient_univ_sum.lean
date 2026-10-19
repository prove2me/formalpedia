-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/0f170f03-2c1a-4e43-ad46-1ba892fd3abe

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
    (k e : ℕ) (hk : 0 < k) :
    (∑ n ∈ Finset.range (k * e),
      homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e n Finset.univ) =
      e ^ k := by
  classical
  let f : (Fin k → Fin e) → ℕ := fun a => ∑ i : Fin k, (a i : ℕ)
  have hf :
      ((Finset.univ : Finset (Fin k → Fin e)) : Set (Fin k → Fin e)).MapsTo f
        (Finset.range (k * e) : Set ℕ) := by
    intro a _
    change f a ∈ Finset.range (k * e)
    apply Finset.mem_range.mpr
    have hstrict :
        (∑ i : Fin k, (a i : ℕ)) < ∑ _i : Fin k, e := by
      apply Finset.sum_lt_sum
      · intro i _
        exact Nat.le_of_lt (a i).isLt
      · refine ⟨⟨0, hk⟩, Finset.mem_univ _, ?_⟩
        exact (a ⟨0, hk⟩).isLt
    simpa [f] using hstrict
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin k → Fin e)))
    (t := Finset.range (k * e)) hf
  change
    Fintype.card (Fin k → Fin e) =
      ∑ n ∈ Finset.range (k * e),
        ((Finset.univ : Finset (Fin k → Fin e)).filter
          (fun a => f a = n)).card at hcard
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hcard
  simp_rw [homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ]
  simpa [homogeneousMapAllKBoxHilbertCoefficient, f] using hcard.symm
end PermanentRollout
