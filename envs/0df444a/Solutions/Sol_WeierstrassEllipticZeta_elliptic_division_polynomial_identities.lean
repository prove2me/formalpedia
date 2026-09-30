-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_division_polynomial_identities
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T19:33:20.265714+00:00
-- url     : https://prove2.me/submissions/ef4935a5-aa68-472c-b6f4-31e7b2875bc7

import Theorems.Thm_WeierstrassEllipticZeta_division_sigma_multiplication
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_division_wp_identities
import Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_addition_data

open WeierstrassEllipticZeta

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
    EllipticDivisionPolynomialIdentities L u := by
  obtain ⟨S⟩ := exists_elliptic_sigma_addition_data L h_zeta_deriv h_zeta_addition
  have hwp := elliptic_division_wp_identities L h_wp_addition
  have hu : u ∉ L.lattice := by simpa using h_regular 1 (by omega)
  intro n hn
  have hs := division_sigma_multiplication L S h_zeta_deriv hwp u n hn
    (fun k hk _ => h_regular k hk)
  have hident := hwp n hn u hu (h_regular n hn) hs.2.1
  exact ⟨hs.2.1, hident.1, hident.2, hs.2.2⟩
