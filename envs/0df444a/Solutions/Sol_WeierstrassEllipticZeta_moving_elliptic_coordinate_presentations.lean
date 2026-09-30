-- Prove2me | solution 1 for WeierstrassEllipticZeta.moving_elliptic_coordinate_presentations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T17:40:05.036656+00:00
-- url     : https://prove2.me/submissions/3eb4995f-cd04-4d93-80e4-4593bec8daa2

import Theorems.Thm_WeierstrassEllipticZeta_specialize_moving_elliptic_coordinates
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_generator_polynomial_presentations

open WeierstrassEllipticZeta
open scoped Polynomial

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
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
    (θ ν : ℂ) (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_generators : ∀ j : Fin 9, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![zetaQuasiPeriod L ω, L.g₂ / 4, L.g₃ / 4,
          L.weierstrassP u₁, L.derivWeierstrassP u₁, weierstrassZeta L u₁,
          L.weierstrassP u₂, L.derivWeierstrassP u₂, weierstrassZeta L u₂] j)) :
    AuxiliaryMovingCoordinateData L ω u₁ u₂ θ ν := by
  have h_polynomials := elliptic_generator_polynomial_presentations L ω u₁ u₂
    h_grid h_zeta_deriv h_zeta_addition h_wp_addition
  apply specialize_moving_elliptic_coordinates L ω u₁ u₂ θ ν d hd _ h_polynomials
  simpa only [ellipticArithmeticGenerators] using h_generators
