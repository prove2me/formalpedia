-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_reduced_jet_systems
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T13:10:30.978478+00:00
-- url     : https://prove2.me/submissions/21721e46-bc1c-4439-ae96-933f393984b5

import Theorems.Thm_TranscendenceTheory_finite_zeros_derivative_bound
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_interpolating_jets
import Definitions.Def_WeierstrassEllipticZeta_GridInterpolation

noncomputable section

open scoped Topology
open Filter Metric Set

namespace WeierstrassEllipticZeta

private theorem grid_interpolation_of_regular_grid (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂) :
    AuxiliaryGridInterpolationData ω u₁ u₂ := by
  intro A T f G ψ hG hf hψ hGf hjet r R C hr hrR hrad hC
  have hzero : ∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A,
      ∀ j < T, iteratedDeriv j G x = 0 := by
    intro x hx
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hG x trivial)).1
    have hfT := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf x hx)).2
      (hjet x hx)
    rw [analyticOrderAt_congr (hGf x hx)]
    change (T : ℕ∞) ≤ analyticOrderAt (ψ * f) x
    rw [analyticOrderAt_mul (hψ x hx) (hf x hx)]
    exact hfT.trans le_add_self
  have hsmall := TranscendenceTheory.finite_zeros_derivative_bound G hG
    (shiftedAuxiliaryGrid u₁ u₂ ω A) (fun _ => T) hzero r R C hr hrR
    (fun x hx => (h_grid.shifted_grid_radius A x hx).trans hrad) hC
  simpa [Finset.sum_const_nat, h_grid.card_shifted_grid, mul_comm] using hsmall

end WeierstrassEllipticZeta

open scoped Polynomial
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
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2)
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (ν : ℂ)
    (g : ℤ[X][X]) (hg_monic : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_kernel : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
    (h_jet_systems : ReducedArithmeticJetSystemData L θ ν g)
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
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ S : TranscendenceTheory.ComplexAuxiliarySystem
          θ ν a ((3 + ‖θ‖ + ‖ν‖) * a) c N,
          S.yDegree < g.natDegree := by
  have h_interpolation := grid_interpolation_of_regular_grid L ω u₁ u₂ h_grid
  exact exists_complex_auxiliary_systems_from_interpolating_jets L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g hg_monic hg_degree hg_kernel
    h_jet_systems h_interpolation d hd h_data
