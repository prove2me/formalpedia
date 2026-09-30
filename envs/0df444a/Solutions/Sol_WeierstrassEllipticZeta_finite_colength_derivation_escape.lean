-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_colength_derivation_escape
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T15:51:06.860745+00:00
-- url     : https://prove2.me/submissions/63c4e611-6f9b-4757-8f2b-af1ae307b3c1

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section


private lemma finite_algebra_derivation_no_time
    (B : Type*) [CommRing B] [Algebra ℂ B] [FiniteDimensional ℂ B]
    (d : Derivation ℂ B B) (u : B) (hu : d u = 1) : Subsingleton B := by
  let T : B →ₗ[ℂ] B := LinearMap.mul ℂ B u
  have hcomm : d.toLinearMap * T - T * d.toLinearMap = 1 := by
    ext x
    change d (u * x) - u * d x = x
    rw [d.leibniz, hu]
    simp [smul_eq_mul]
  have htrace : (Module.finrank ℂ B : ℂ) = 0 := by
    have h := congrArg (LinearMap.trace ℂ B) hcomm
    rw [map_sub, LinearMap.trace_mul_comm, sub_self, LinearMap.trace_one] at h
    exact h.symm
  have hdim : Module.finrank ℂ B = 0 := Nat.cast_eq_zero.mp htrace
  exact (Module.finrank_zero_iff (R := ℂ)).mp hdim

theorem solution
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (t : A) (ht : D t = 1)
    (I : Ideal A) [FiniteDimensional ℂ (A ⧸ I)] (hI : I ≠ ⊤) :
    ∃ p : A, p ∈ I ∧ D p ∉ I := by
  classical
  by_contra hnone
  have hstable (p : A) (hp : p ∈ I) : D p ∈ I := by
    by_contra hdp
    exact hnone ⟨p, hp, hdp⟩
  let π : A →ₐ[ℂ] A ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hker (p : A) (hp : π p = 0) : π (D p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (hstable p (Ideal.Quotient.eq_zero_iff_mem.mp hp))
  let d : Derivation ℂ (A ⧸ I) (A ⧸ I) :=
    D.liftOfSurjective (Ideal.Quotient.mkₐ_surjective ℂ I) hker
  have hdt : d (π t) = 1 := by
    rw [Derivation.liftOfSurjective_apply]
    simp only [ht, map_one]
  exact hI (Ideal.Quotient.subsingleton_iff.mp
    (finite_algebra_derivation_no_time (A ⧸ I) d (π t) hdt))

