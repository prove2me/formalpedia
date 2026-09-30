-- Prove2me | solution 1 for WeierstrassEllipticZeta.auxiliary_nonlattice_coordinate_presentations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T17:19:30.19272+00:00
-- url     : https://prove2.me/submissions/daaf88a3-2d56-4d8c-a5d9-4f3d5aaa1557

import Theorems.Thm_WeierstrassEllipticZeta_complete_auxiliary_nonlattice_coordinates
import Theorems.Thm_WeierstrassEllipticZeta_moving_elliptic_coordinate_presentations

import Mathlib.Tactic.FinCases

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
    (θ ν : ℂ) (g : ℤ[X][X])
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_data : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.natDegree < g.natDegree ∧
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i)) :
    AuxiliaryNonlatticeCoordinateData L ω u₁ u₂ θ ν := by
  have h_fixed : ∀ j : Fin 7, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![u₁ / 2, u₂, ω, weierstrassZeta L (u₁ / 2), L.weierstrassP (u₁ / 2),
          L.derivWeierstrassP (u₁ / 2), deriv L.derivWeierstrassP (u₁ / 2)] j) := by
    intro j
    obtain ⟨p, _, hp⟩ := h_data (![4, 5, 2, 6, 7, 8, 9] j)
    refine ⟨p, ?_⟩
    fin_cases j <;> simpa using hp
  have h_generators : ∀ j : Fin 9, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![zetaQuasiPeriod L ω, L.g₂ / 4, L.g₃ / 4,
          L.weierstrassP u₁, L.derivWeierstrassP u₁, weierstrassZeta L u₁,
          L.weierstrassP u₂, L.derivWeierstrassP u₂, weierstrassZeta L u₂] j) := by
    intro j
    obtain ⟨p, _, hp⟩ := h_data (![3, 0, 1, 10, 11, 13, 14, 15, 17] j)
    refine ⟨p, ?_⟩
    fin_cases j <;> simpa using hp
  have h_moving := moving_elliptic_coordinate_presentations L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition θ ν d hd h_generators
  exact complete_auxiliary_nonlattice_coordinates L ω u₁ u₂ θ ν d hd h_fixed h_moving
