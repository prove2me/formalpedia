-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_generator_polynomial_presentations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T18:14:39.077977+00:00
-- url     : https://prove2.me/submissions/9abc6271-186b-4fe0-91b4-15000b4445a8

import Theorems.Thm_WeierstrassEllipticZeta_compose_elliptic_generator_polynomials
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_multiple_polynomial_presentations

open WeierstrassEllipticZeta

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
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2) :
    EllipticGeneratorPolynomialData L ω u₁ u₂ := by
  have hregular₁ : ∀ n : ℕ, 0 < n → (n : ℂ) * u₁ ∉ L.lattice := by
    intro n hn hL
    have hh : integerGridPoint u₁ u₂ ω ![(n : ℤ), 0, 0] ∈ L.lattice := by
      simpa [integerGridPoint] using hL
    have hzero : (n : ℤ) = 0 := ((h_grid.lattice_iff _).mp hh).1
    have hn0 : n = 0 := by exact_mod_cast hzero
    omega
  have hregular₂ : ∀ n : ℕ, 0 < n → (n : ℂ) * u₂ ∉ L.lattice := by
    intro n hn hL
    have hh : integerGridPoint u₁ u₂ ω ![0, (n : ℤ), 0] ∈ L.lattice := by
      simpa [integerGridPoint] using hL
    have hzero : (n : ℤ) = 0 := ((h_grid.lattice_iff _).mp hh).2
    have hn0 : n = 0 := by exact_mod_cast hzero
    omega
  have h₁ := elliptic_multiple_polynomial_presentations L u₁ hregular₁
    h_zeta_deriv h_zeta_addition h_wp_addition
  have h₂ := elliptic_multiple_polynomial_presentations L u₂ hregular₂
    h_zeta_deriv h_zeta_addition h_wp_addition
  exact compose_elliptic_generator_polynomials L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition h₁ h₂
