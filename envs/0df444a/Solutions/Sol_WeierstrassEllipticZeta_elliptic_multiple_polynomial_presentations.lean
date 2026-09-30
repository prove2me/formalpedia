-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_multiple_polynomial_presentations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T18:48:42.114704+00:00
-- url     : https://prove2.me/submissions/612d9dc3-4d65-429a-8bab-e008ad39cd4e

import Theorems.Thm_WeierstrassEllipticZeta_division_multiple_polynomial_bounds
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_division_polynomial_identities
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

open WeierstrassEllipticZeta MvPolynomial

theorem solution
    (L : PeriodPair) (u : ℂ)
    (h_regular : ∀ n : ℕ, 0 < n → (n : ℂ) * u ∉ L.lattice)
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
    EllipticMultiplePolynomialData L u := by
  have hi := elliptic_division_polynomial_identities L u h_regular
    h_zeta_deriv h_zeta_addition h_wp_addition
  obtain ⟨C, H, hC, hH, hb⟩ := division_multiple_polynomial_bounds
  refine ⟨C, H, hC, hH, ?_⟩
  intro n hn
  obtain ⟨hd, hl, hnd, hnl⟩ := hb n hn
  obtain ⟨hf, hp, hdp, hz⟩ := hi n hn
  dsimp only at hf hp hdp hz
  refine ⟨{
    numerator := ellipticDivisionNumerator n
    denominator := ellipticDivisionDenominator n
    numerator_degree := hnd
    denominator_degree := hd
    numerator_length := hnl
    denominator_length := hl
    denominator_ne_zero := ?_
    evaluation := ?_
  }⟩
  · simp only [ellipticDivisionDenominator, eval₂_mul, eval₂_pow,
      map_natCast, eval₂_natCast]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) (pow_ne_zero 4 hf)
  · intro j
    have hx : ellipticMultipleGenerators L u 2 = L.weierstrassP u := rfl
    have hz₀ : ellipticMultipleGenerators L u 4 = weierstrassZeta L u := rfl
    fin_cases j
    · change eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L u)
        (MvPolynomial.C ((n : ℤ) ^ 2) * ellipticDivisionPolynomial n ^ 4 * X 4 +
          ellipticDivisionPolynomial n ^ 3 *
            ellipticMultipleDerivation (ellipticDivisionPolynomial n)) =
        eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L u)
          (ellipticDivisionDenominator n) * weierstrassZeta L (n * u)
      simp only [ellipticDivisionDenominator, eval₂_add, eval₂_mul, eval₂_pow,
        eval₂_X, map_pow, map_natCast, eval₂_natCast, hz₀]
      linear_combination -(eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L u)
        (ellipticDivisionPolynomial n)) ^ 3 * hz
    · change eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L u)
        (MvPolynomial.C (n : ℤ) * (X 2 * ellipticDivisionPolynomial n ^ 2 -
          ellipticDivisionPolynomial (n - 1) * ellipticDivisionPolynomial (n + 1)) *
            ellipticDivisionPolynomial n ^ 2) =
        eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L u)
          (ellipticDivisionDenominator n) * L.weierstrassP (n * u)
      simp only [ellipticDivisionDenominator, eval₂_sub, eval₂_mul, eval₂_pow,
        eval₂_X, map_natCast, eval₂_natCast, hx]
      linear_combination -(n : ℂ) * (eval₂ (Int.castRingHom ℂ)
        (ellipticMultipleGenerators L u) (ellipticDivisionPolynomial n)) ^ 2 * hp
    · change eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L u)
        (MvPolynomial.C (n : ℤ) * ellipticDivisionPolynomial (2 * n)) =
        eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L u)
          (ellipticDivisionDenominator n) * L.derivWeierstrassP (n * u)
      simp only [ellipticDivisionDenominator, eval₂_mul, eval₂_pow, map_natCast, eval₂_natCast]
      linear_combination -(n : ℂ) * hdp
