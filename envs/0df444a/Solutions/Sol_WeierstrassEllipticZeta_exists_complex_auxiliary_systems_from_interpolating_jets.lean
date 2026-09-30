-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_interpolating_jets
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T13:37:24.426758+00:00
-- url     : https://prove2.me/submissions/09e301b7-fdeb-4977-9f64-ade8167394ac

import Theorems.Thm_TranscendenceTheory_exists_entire_monomial_regularization
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_entire_regularization
import Definitions.Def_WeierstrassEllipticZeta_EntireRegularization
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FinCases

noncomputable section

open Filter Metric Set
open scoped Topology

namespace WeierstrassEllipticZeta

private theorem elliptic_regularization_of_interpolation (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_interpolation : AuxiliaryGridInterpolationData ω u₁ u₂) :
    EllipticRegularizationData L ω u₁ u₂ := by
  intro σ S hσ hS hrel ι _ v c l e D K hl he
  have hweight (i : ι) : ∑ j : Fin 3, (j.val + 1) * e i j ≤ K := by
    simpa [Fin.sum_univ_succ, add_assoc] using he i
  obtain ⟨G, hG, hEq, hbound⟩ :=
    TranscendenceTheory.exists_entire_monomial_regularization
      (L.lattice : Set ℂ)ᶜ σ (fun j z => ellipticPoleCoordinates L z j) S
      hσ hS (fun j => j.val + 1) (fun j => by omega) hrel v c l e D K hl hweight
  refine ⟨G, hG, hEq, hbound, ?_⟩
  intro A T r R B hr hR hB hrad hbasic hjets
  have hZ : AnalyticOnNhd ℂ (weierstrassZeta L) (L.lattice : Set ℂ)ᶜ :=
    (show DifferentiableOn ℂ (weierstrassZeta L) (L.lattice : Set ℂ)ᶜ from
      fun z hz => (hzeta z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl
  have hφ (z : ℂ) (hz : z ∉ L.lattice) (j : Fin 3) :
      AnalyticAt ℂ (fun z => ellipticPoleCoordinates L z j) z := by
    fin_cases j
    · exact hZ z hz
    · exact L.analyticOnNhd_weierstrassP z hz
    · exact L.analyticOnNhd_derivWeierstrassP z hz
  have hf (z : ℂ) (hz : z ∉ L.lattice) :
      AnalyticAt ℂ (ellipticRegularizationSum L v c l e) z := by
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (analyticAt_const.mul ((analyticAt_id.add analyticAt_const).pow _)).mul
      (Finset.analyticAt_fun_prod _ fun j _ => (hφ z hz j).pow _)
  have hlocal (x : ℂ) (hx : x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A) :
      G =ᶠ[𝓝 x] fun z => σ z ^ K * ellipticRegularizationSum L v c l e z := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      (h_grid.shifted_grid_regular A x hx)] with z hz
    exact hEq z hz
  exact h_interpolation A T (ellipticRegularizationSum L v c l e) G
    (fun z => σ z ^ K) hG
    (fun x hx => hf x (h_grid.shifted_grid_regular A x hx))
    (fun x _ => (hσ x trivial).pow K) hlocal hjets r R
    ((∑ i, ‖c i‖) * (max 1 (R + ‖v‖)) ^ D * B ^ K)
    hr hR hrad (fun z hz => hbound R B hB hbasic z (by
      simpa only [mem_sphere, dist_zero_right] using le_of_eq hz))

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
    (h_interpolation : AuxiliaryGridInterpolationData ω u₁ u₂)
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
  have h_regularization := elliptic_regularization_of_interpolation L ω u₁ u₂ h_grid
    h_zeta_deriv h_interpolation
  exact exists_complex_auxiliary_systems_from_entire_regularization L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g hg_monic hg_degree hg_kernel
    h_jet_systems h_interpolation h_regularization d hd h_data
