-- Prove2me | solution 1 for WeierstrassEllipticZeta.small_polynomials_of_algebraic_values
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T03:17:16.565877+00:00
-- url     : https://prove2.me/submissions/ac142003-a9c7-4903-9e11-48c64f5c8deb

import Theorems.Thm_WeierstrassEllipticZeta_small_integral_elements_of_algebraic_values
import Theorems.Thm_TranscendenceTheory_small_polynomials_of_small_integral_elements

open Polynomial Module Filter WeierstrassEllipticZeta
open scoped Polynomial

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω_ne : ω ≠ 0) (hω_period : ω ∈ L.lattice)
    (h_linearIndependent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (h_wp_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2)
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (h_values : ∀ i, IsAlgebraic (Algebra.adjoin ℚ {θ})
      (theoremOneValues L ω u₁ u₂ i)) :
    ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ p : ℤ[X],
        (p.natDegree : ℝ) ≤ A * N ∧
        (∀ k, |(p.coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
        0 < ‖Polynomial.aeval θ p‖ ∧
        ‖Polynomial.aeval θ p‖ ≤ Real.exp (-10 * (A * N) ^ 2) := by
  obtain ⟨S, hθS, d, b, hb, C, c, hC, hc, hsmall⟩ :=
    small_integral_elements_of_algebraic_values L ω u₁ u₂ hω_ne hω_period
      h_linearIndependent h_intersection h_zeta_deriv h_zeta_addition h_wp_addition θ hθ h_values
  let : Algebra ℤ[X] S := (Polynomial.aeval (⟨θ, hθS⟩ : S)).toAlgebra
  have hθZ : Transcendental ℤ θ := hθ.restrictScalars (algebraMap ℤ ℚ).injective_int
  apply TranscendenceTheory.small_polynomials_of_small_integral_elements
    θ hθZ S.subtype _ d b hb C c hC hc hsmall
  intro p
  change (↑(Polynomial.aeval (⟨θ, hθS⟩ : S) p) : ℂ) = Polynomial.aeval θ p
  simpa using (Polynomial.aeval_algHom_apply (S.subtype.toIntAlgHom) (⟨θ, hθS⟩ : S) p).symm
