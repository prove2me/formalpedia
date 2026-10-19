-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_insert_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/2246f0ba-52cd-4279-bd38-06b67c5f7b93

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
    (hj : j ∉ restricted) :
    homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e (e + n)
        (insert j restricted) +
      homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e n restricted =
      homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e (e + n) restricted := by
  classical
  let s : Finset (Fin k →₀ ℕ) :=
    ((Finset.univ : Finset (Fin k)).finsuppAntidiag (e + n)).filter
      (fun d => ∀ i ∈ restricted, d i < e)
  let t : Finset (Fin k →₀ ℕ) :=
    ((Finset.univ : Finset (Fin k)).finsuppAntidiag n).filter
      (fun d => ∀ i ∈ restricted, d i < e)
  have hgood :
      (s.filter (fun d => d j < e)).card =
        homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e (e + n)
          (insert j restricted) := by
    unfold homogeneousMapAllKBoundedHomogeneousHilbertCoefficient
    congr 1
    ext d
    simp [s, and_left_comm, and_comm]
  have hbad :
      t.card = (s.filter (fun d => ¬ d j < e)).card := by
    refine Finset.card_bij (fun d _ => d + Finsupp.single j e) ?_ ?_ ?_
    · intro d hd
      simp only [t, Finset.mem_filter, Finset.mem_finsuppAntidiag,
        Finset.subset_univ, and_true] at hd
      simp only [s, Finset.mem_filter, Finset.mem_finsuppAntidiag,
        Finset.subset_univ, and_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have hdegree : d.degree = n := by
          simpa [Finsupp.degree_eq_sum] using hd.1
        have hsum : (d + Finsupp.single j e).degree = n + e := by
          simp [hdegree, Finsupp.degree_single]
        simpa [Finsupp.degree_eq_sum, Nat.add_comm] using hsum
      · intro i hi
        have hij : j ≠ i := by
          intro h
          exact hj (h ▸ hi)
        simpa [Finsupp.single_apply, hij] using hd.2 i hi
      · simp
    · intro d₁ _ d₂ _ h
      exact add_right_cancel h
    · intro d hd
      simp only [s, Finset.mem_filter, Finset.mem_finsuppAntidiag,
        Finset.subset_univ, and_true] at hd
      let a : Fin k →₀ ℕ := d - Finsupp.single j e
      have hle : e ≤ d j := by omega
      have hrecover : a + Finsupp.single j e = d := by
        ext i
        by_cases hi : j = i
        · subst i
          simpa [a] using Nat.sub_add_cancel hle
        · simp [a, hi]
      refine ⟨a, ?_, hrecover⟩
      simp only [t, Finset.mem_filter, Finset.mem_finsuppAntidiag,
        Finset.subset_univ, and_true]
      refine ⟨?_, ?_⟩
      · have hdegree : d.degree = e + n := by
          simpa [Finsupp.degree_eq_sum] using hd.1.1
        have hrecoverDegree := congrArg Finsupp.degree hrecover
        have hadegree : a.degree + e = e + n := by
          simpa [Finsupp.degree_single, hdegree] using hrecoverDegree
        have han : a.degree = n := by omega
        simpa [Finsupp.degree_eq_sum] using han
      · intro i hi
        have hji : j ≠ i := by
          intro h
          exact hj (h ▸ hi)
        simpa [a, Finsupp.single_apply, hji] using hd.1.2 i hi
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := s) (fun d : Fin k →₀ ℕ => d j < e)
  change homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e (e + n)
      (insert j restricted) + t.card = s.card
  rw [← hgood, hbad]
  exact hsplit
end PermanentRollout
