-- Prove2me | solution 1 for WeierstrassEllipticZeta.linear_map_unit_multiplier_iff
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T21:27:36.585951+00:00
-- url     : https://prove2.me/submissions/9d7bdd96-2bef-4559-9762-d69226ee23ca

import Mathlib.Algebra.Algebra.Bilinear



theorem solution
    (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (T : A →ₗ[R] A) :
    ((∃! b : A, T = Algebra.lmul R A b) ∧ Function.Bijective T) ↔
      ∃! u : Aˣ, T = Algebra.lmul R A (u : A) := by
  constructor
  · rintro ⟨⟨b, rfl, _⟩, hb⟩
    have hunit : IsUnit b := Algebra.lmul_isUnit_iff.mp
      ((Module.End.isUnit_iff _).mpr hb)
    obtain ⟨u, rfl⟩ := hunit
    refine ⟨u, rfl, ?_⟩
    intro v hv
    apply Units.ext
    exact (Algebra.lmul_injective hv).symm
  · rintro ⟨u, rfl, _⟩
    refine ⟨⟨(u : A), rfl, ?_⟩, ?_⟩
    · intro b hb
      exact (Algebra.lmul_injective hb).symm
    · exact (Module.End.isUnit_iff _).mp
        (Algebra.lmul_isUnit_iff.mpr u.isUnit)

