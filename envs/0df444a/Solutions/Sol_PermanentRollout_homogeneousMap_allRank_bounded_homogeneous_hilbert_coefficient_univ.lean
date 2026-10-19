-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_bounded_homogeneous_hilbert_coefficient_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/5b14ab4a-e701-4f0b-a135-9b4ca4ca3d55

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
    (k e n : ℕ) :
    homogeneousMapAllKBoundedHomogeneousHilbertCoefficient k e n Finset.univ =
      homogeneousMapAllKBoxHilbertCoefficient k e n := by
  classical
  unfold homogeneousMapAllKBoundedHomogeneousHilbertCoefficient
    homogeneousMapAllKBoxHilbertCoefficient
  let s : Finset (Fin k →₀ ℕ) :=
    ((Finset.univ : Finset (Fin k)).finsuppAntidiag n).filter
      (fun d => ∀ i ∈ (Finset.univ : Finset (Fin k)), d i < e)
  let t : Finset (Fin k → Fin e) :=
    (Finset.univ : Finset (Fin k → Fin e)).filter
      (fun a => (∑ i : Fin k, (a i : ℕ)) = n)
  change s.card = t.card
  let φ (d : Fin k →₀ ℕ) (hd : d ∈ s) : Fin k → Fin e :=
    fun i => ⟨d i, (Finset.mem_filter.mp hd).2 i (Finset.mem_univ _)⟩
  refine Finset.card_bij φ ?_ ?_ ?_
  · intro d hd
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
    have hdegree :=
      (Finset.mem_finsuppAntidiag.mp (Finset.mem_filter.mp hd).1).1
    simpa [φ] using hdegree
  · intro d₁ hd₁ d₂ hd₂ h
    apply Finsupp.ext
    intro i
    simpa [φ] using congrArg (fun a : Fin k → Fin e => (a i : ℕ)) h
  · intro a ha
    have ha' : (∑ i : Fin k, (a i : ℕ)) = n := by
      simpa [t] using ha
    let d : Fin k →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))
    have hdapply (i : Fin k) : d i = (a i : ℕ) := by
      simp [d]
    have hd : d ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_finsuppAntidiag,
        Finset.subset_univ, and_true]
      constructor
      · simpa [hdapply] using ha'
      · intro i _
        rw [hdapply]
        exact (a i).isLt
    refine ⟨d, hd, ?_⟩
    funext i
    apply Fin.ext
    exact hdapply i
end PermanentRollout
