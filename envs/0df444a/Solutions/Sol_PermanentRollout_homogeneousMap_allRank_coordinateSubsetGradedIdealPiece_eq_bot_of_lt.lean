-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allRank_coordinateSubsetGradedIdealPiece_eq_bot_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:04.538453+00:00
-- url     : https://prove2.me/submissions/64ee5d5f-23dd-47f7-a0c0-6a451722abad

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousComponent_mul_of_right_isHomogeneous_of_lt

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
    {k e : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (restricted : Finset (Fin k)) (n : ℕ) (hn : n < e) :
    homogeneousMapGradedIdealPiece
      (homogeneousMapAllKCoordinateSubsetIdeal F restricted) n = ⊥ := by
  classical
  apply bot_unique
  intro p hp
  change (p : MvPolynomial (Fin k) ℂ) ∈
    homogeneousMapAllKCoordinateSubsetIdeal F restricted at hp
  have hrange :
      Set.range (fun i : {i : Fin k // i ∈ restricted} => F i.1) =
        F '' (restricted : Set (Fin k)) := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  change (p : MvPolynomial (Fin k) ℂ) ∈
    Ideal.span (F '' (restricted : Set (Fin k))) at hp
  rw [← hrange] at hp
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hp
  have hcomponent := congrArg (MvPolynomial.homogeneousComponent n) hc
  simp only [map_sum] at hcomponent
  have hterms : ∀ i : {i : Fin k // i ∈ restricted},
      MvPolynomial.homogeneousComponent n (c i * F i.1) = 0 :=
    fun i => homogeneousComponent_mul_of_right_isHomogeneous_of_lt
      (c i) (F i.1) (hF i.1) hn
  simp_rw [hterms, Finset.sum_const_zero,
    MvPolynomial.homogeneousComponent_eq_self p.property] at hcomponent
  have hpzero : p = 0 := Subtype.ext hcomponent.symm
  simp [hpzero]
end PermanentRollout
