-- Prove2me | solution 1 for WeierstrassEllipticZeta.small_bivariate_values_of_integral_auxiliary_data
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T09:30:51.760826+00:00
-- url     : https://prove2.me/submissions/26ac7319-6161-40cb-a45f-240d914978fd

import Theorems.Thm_TranscendenceTheory_small_values_of_bounded_bivariate_systems
import Theorems.Thm_WeierstrassEllipticZeta_exists_bounded_auxiliary_systems

open WeierstrassEllipticZeta Polynomial

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
    (ν : ℂ)
    (hν : ∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (Polynomial.aeval θ).toRingHom ν = 0)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_data : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i)) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
        ∀ᶠ N : ℕ in Filter.atTop, ∃ P : ℤ[X][X],
          (P.natDegree : ℝ) ≤ A * N ∧
          (∀ j, ((P.coeff j).natDegree : ℝ) ≤ A * N) ∧
          (∀ j k, |((P.coeff j).coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
          P.eval₂ (Polynomial.aeval θ).toRingHom ν ≠ 0 ∧
          ‖P.eval₂ (Polynomial.aeval θ).toRingHom ν‖ ≤
            Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by
  apply TranscendenceTheory.small_values_of_bounded_bivariate_systems θ ν
  exact exists_bounded_auxiliary_systems L ω u₁ u₂ hω_ne hω_period
    h_linearIndependent h_intersection h_zeta_deriv h_zeta_addition h_wp_addition
    θ hθ ν hν d hd h_data
