-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_entire_regularization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T14:06:40.782347+00:00
-- url     : https://prove2.me/submissions/f506f61b-01c7-4116-a3a3-378cbafb9c70

import Theorems.Thm_WeierstrassEllipticZeta_cleared_addition_entire_growth
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_cleared_entire_data
import Definitions.Def_WeierstrassEllipticZeta_ClearedEntire
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section

open Filter Metric Set
open scoped Topology

namespace WeierstrassEllipticZeta

private theorem cleared_addition_entire_data (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (hZ : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (hP : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2)
    (h_interpolation : AuxiliaryGridInterpolationData ω u₁ u₂) :
    ClearedAdditionEntireData L ω u₁ u₂ := by
  intro σ S hσ hS hrel ι _ v hv c l₀ l₂ l₃ D M h₀ h₂ h₃
  obtain ⟨G, hG, hEq, hbound⟩ := cleared_addition_entire_growth L hZ hP σ S hσ hS hrel
    v hv c l₀ l₂ l₃ D M h₀ h₂ h₃
  refine ⟨G, hG, hEq, hbound, ?_⟩
  intro A T r R B hr hR hB hrad hbasic hshift hjets
  have hZan : AnalyticOnNhd ℂ (weierstrassZeta L) (L.lattice : Set ℂ)ᶜ :=
    (show DifferentiableOn ℂ (weierstrassZeta L) (L.lattice : Set ℂ)ᶜ from
      fun z hz => (hzeta z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl
  have hf (x : ℂ) (hx : x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A) :
      AnalyticAt ℂ (clearedAuxiliarySum L v c l₀ l₂ l₃ M) x := by
    have hPx := L.analyticOnNhd_weierstrassP x (h_grid.shifted_grid_regular A x hx)
    have hadd : AnalyticAt ℂ (fun z => z + v) x := analyticAt_id.add analyticAt_const
    have hPv : AnalyticAt ℂ (fun z => L.weierstrassP (z + v)) x :=
      (L.analyticOnNhd_weierstrassP (x + v) (hshift x hx)).comp
        (f := fun z : ℂ => z + v) (x := x) hadd
    have hZv : AnalyticAt ℂ (fun z => weierstrassZeta L (z + v)) x :=
      (hZan (x + v) (hshift x hx)).comp (f := fun z : ℂ => z + v) (x := x) hadd
    unfold clearedAuxiliarySum
    apply Finset.analyticAt_fun_sum
    intro i _
    apply analyticAt_const.mul
    unfold clearedAdditionMonomial
    fun_prop
  have hlocal (x : ℂ) (hx : x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A) :
      G =ᶠ[𝓝 x] fun z => σ z ^ (15 * M) * clearedAuxiliarySum L v c l₀ l₂ l₃ M z := by
    have hnear : ∀ᶠ z in 𝓝 x, z + v ∉ L.lattice :=
      (continuousAt_id.add_const v).eventually
        (L.isClosed_lattice.isOpen_compl.mem_nhds (hshift x hx))
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      (h_grid.shifted_grid_regular A x hx), hnear] with z hz hzv
    exact hEq z hz hzv
  exact h_interpolation A T (clearedAuxiliarySum L v c l₀ l₂ l₃ M) G
    (fun z => σ z ^ (15 * M)) hG hf (fun x _ => (hσ x trivial).pow _) hlocal hjets
    r R (clearedAuxiliaryBound L v c D M R B) hr hR hrad
    (fun z hz => hbound R B hB hbasic z (by
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
    (h_regularization : EllipticRegularizationData L ω u₁ u₂)
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
  have h_cleared_entire := cleared_addition_entire_data L ω u₁ u₂ h_grid h_zeta_deriv
    h_zeta_addition h_wp_addition h_interpolation
  exact exists_complex_auxiliary_systems_from_cleared_entire_data L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g hg_monic hg_degree hg_kernel
    h_jet_systems h_interpolation h_regularization h_cleared_entire d hd h_data
