-- Prove2me | solution 1 for WeierstrassEllipticZeta.adjoin_dimension_generation_criterion
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T17:26:01.886207+00:00
-- url     : https://prove2.me/submissions/949265e3-e0a8-4036-872d-b898ce45fe18

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic



theorem solution
    (K A : Type*) [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]
    (x : A) (n d : ℕ) (hdim : Module.finrank K (Algebra.adjoin K ({x} : Set A)) = n)
    (hdimA : Module.finrank K A = d) :
    n ≤ d ∧
      (n = d ↔ Algebra.adjoin K ({x} : Set A) = ⊤) ∧
      (n = d ↔
        Function.Surjective (fun q : Polynomial K => q.eval₂ (algebraMap K A) x)) ∧
      (n < d ↔
        ∃ y : A, ∀ q : Polynomial K, q.eval₂ (algebraMap K A) x ≠ y) := by
  subst d
  classical
  let B := Algebra.adjoin K ({x} : Set A)
  have hle : n ≤ Module.finrank K A := by
    rw [← hdim]
    exact B.toSubmodule.finrank_le
  have htop : n = Module.finrank K A ↔ B = ⊤ := by
    constructor
    · intro h
      apply Algebra.toSubmodule_eq_top.mp
      exact Submodule.eq_top_of_finrank_eq (hdim.trans h)
    · intro h
      rw [← hdim]
      change Module.finrank K B = _
      rw [h]
      exact (Subalgebra.topEquiv.toLinearEquiv).finrank_eq
  have hsurj : B = ⊤ ↔
      Function.Surjective (fun q : Polynomial K => q.eval₂ (algebraMap K A) x) := by
    change Algebra.adjoin K ({x} : Set A) = ⊤ ↔ _
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
    rfl
  refine ⟨hle, htop, htop.trans hsurj, ?_⟩
  rw [lt_iff_le_and_ne, and_iff_right hle]
  simp only [ne_eq, htop, hsurj, Function.Surjective, not_forall, not_exists]

