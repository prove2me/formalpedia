-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_colength_bounded_time_escape
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T16:03:59.705559+00:00
-- url     : https://prove2.me/submissions/0ac39db1-b264-4686-8aa2-8b1be0a21c98

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Minpoly.Finite

noncomputable section



theorem solution
    (A : Type*) [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (t : A) (ht : D t = 1)
    (I : Ideal A) [FiniteDimensional ℂ (A ⧸ I)] (hI : I ≠ ⊤) :
    ∃ g : Polynomial ℂ,
      g.Monic ∧ 0 < g.natDegree ∧
      g.natDegree ≤ Module.finrank ℂ (A ⧸ I) ∧
      (∀ q : Polynomial ℂ, Polynomial.aeval t q ∈ I ↔ g ∣ q) ∧
      Polynomial.aeval t g ∈ I ∧
      D (Polynomial.aeval t g) = Polynomial.aeval t g.derivative ∧
      g.derivative.natDegree < g.natDegree ∧
      D (Polynomial.aeval t g) ∉ I := by
  let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let π : A →ₐ[ℂ] A ⧸ I := Ideal.Quotient.mkₐ ℂ I
  let g : Polynomial ℂ := minpoly ℂ (π t)
  have hint : IsIntegral ℂ (π t) := IsIntegral.of_finite ℂ (π t)
  have hpos : 0 < g.natDegree := minpoly.natDegree_pos hint
  have hmem (q : Polynomial ℂ) : Polynomial.aeval t q ∈ I ↔ g ∣ q := by
    change Polynomial.aeval t q ∈ I ↔ minpoly ℂ (π t) ∣ q
    rw [minpoly.dvd_iff, Polynomial.aeval_algHom_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.symm
  have hderiv : D (Polynomial.aeval t g) = Polynomial.aeval t g.derivative := by
    simp only [Derivation.map_aeval, ht, smul_eq_mul, mul_one]
  have hlt : g.derivative.natDegree < g.natDegree :=
    Polynomial.natDegree_derivative_lt (Nat.ne_of_gt hpos)
  refine ⟨g, minpoly.monic hint, hpos, minpoly.natDegree_le (π t), hmem,
    (hmem g).mpr dvd_rfl, hderiv, hlt, ?_⟩
  intro hbad
  rw [hderiv, hmem] at hbad
  exact (not_le_of_gt hlt) (Polynomial.natDegree_le_of_dvd hbad
    (Polynomial.derivative_ne_zero.mpr (Nat.ne_of_gt hpos)))

