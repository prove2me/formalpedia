-- Prove2me | solution 1 for WeierstrassEllipticZeta.small_integral_elements_of_algebraic_values
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T04:06:08.806626+00:00
-- url     : https://prove2.me/submissions/143340ed-bd43-4ae3-979a-db50352cb572

import Theorems.Thm_WeierstrassEllipticZeta_small_bivariate_values_of_algebraic_values
import Theorems.Thm_TranscendenceTheory_small_integral_coordinates_of_bivariate_values

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
    ∃ (S : Subring ℂ) (hθS : θ ∈ S) (d : ℕ),
      letI : Algebra ℤ[X] S := (Polynomial.aeval (⟨θ, hθS⟩ : S)).toAlgebra
      ∃ b : Module.Basis (Fin (d + 1)) ℤ[X] S, b 0 = 1 ∧
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ᶠ N : ℕ in Filter.atTop, ∃ x : S, x ≠ 0 ∧
            (∀ i, ((b.repr x i).natDegree : ℝ) ≤ C * N) ∧
            (∀ i k, |((b.repr x i).coeff k : ℝ)| ≤ Real.exp (C * N)) ∧
            ‖(x : ℂ)‖ ≤ Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by
  obtain ⟨ν, hν, A, c, hA, hc, hsmall⟩ :=
    small_bivariate_values_of_algebraic_values L ω u₁ u₂ hω_ne hω_period
      h_linearIndependent h_intersection h_zeta_deriv h_zeta_addition h_wp_addition θ hθ h_values
  have hθZ : Transcendental ℤ θ := hθ.restrictScalars (algebraMap ℤ ℚ).injective_int
  exact TranscendenceTheory.small_integral_coordinates_of_bivariate_values θ ν hθZ hν A c hA hc hsmall
