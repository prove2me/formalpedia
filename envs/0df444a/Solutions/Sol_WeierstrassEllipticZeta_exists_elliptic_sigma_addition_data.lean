-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_elliptic_sigma_addition_data
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T20:37:00.279977+00:00
-- url     : https://prove2.me/submissions/5e8dd343-7403-4ed1-afda-cb0b25010729

import Theorems.Thm_WeierstrassEllipticZeta_sigma_addition_from_differential
import Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_differential_data

open WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z) :
    Nonempty (EllipticSigmaData L) := by
  obtain ⟨S⟩ := exists_elliptic_sigma_differential_data L
  have hs := sigma_addition_from_differential L S h_zeta_deriv h_zeta_addition
  exact ⟨{
    sigma := S.sigma
    zero := S.zero
    deriv_zero := S.deriv_zero
    ne_zero := hs.1
    hasDerivAt := S.hasDerivAt
    addition := hs.2
  }⟩
