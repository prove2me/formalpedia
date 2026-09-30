-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_arithmetic_jets
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T12:26:31.569834+00:00
-- url     : https://prove2.me/submissions/5278ae13-8aa1-412c-985b-5972ea20fa79

import Theorems.Thm_TranscendenceTheory_bivariate_monic_reduction_bound
import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_reduced_arithmetic_jets
import Definitions.Def_WeierstrassEllipticZeta_ArithmeticJets
import Definitions.Def_WeierstrassEllipticZeta_ReducedArithmeticJets

noncomputable section

open scoped Polynomial

namespace WeierstrassEllipticZeta

private theorem reduced_arithmetic_jets_of_arithmetic_jets (L : PeriodPair)
    (h_arithmetic : ArithmeticJetData L) (θ ν : ℂ)
    (g : ℤ[X][X]) (hg : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_zero : g.eval₂ (Polynomial.aeval θ).toRingHom ν = 0) :
    ReducedArithmeticJetData L θ ν g := by
  classical
  let B := g.support.sup fun i => (g.coeff i).natDegree
  let H := 1 + ∑ i ∈ g.support, ∑ j ∈ (g.coeff i).support,
    ((g.coeff i).coeff j).natAbs
  have hB (i : ℕ) : (g.coeff i).natDegree ≤ B := by
    by_cases hi : i ∈ g.support
    · exact Finset.le_sup (f := fun i => (g.coeff i).natDegree) hi
    · simp [Polynomial.notMem_support_iff.mp hi]
  refine ⟨B + 1, H, by omega, by dsimp [H]; omega, ?_⟩
  intro M L₀ l₀ l₂ l₃ n hl₀ hl₂ hl₃
  dsimp only
  intro s q d h hsdeg hqdeg hslen hqlen
  obtain ⟨p, hpdeg, hplen, hpeval⟩ :=
    h_arithmetic M L₀ l₀ l₂ l₃ n hl₀ hl₂ hl₃ s q d h hsdeg hqdeg hslen hqlen
  obtain ⟨r, hrY, hrX, hrlen, hreval⟩ :=
    TranscendenceTheory.bivariate_monic_reduction_bound g hg hg_degree B hB p
  refine ⟨r, hrY, ?_, ?_, ?_⟩
  · intro j
    exact (hrX j).trans (Nat.mul_le_mul_left _ hpdeg)
  · apply hrlen.trans
    exact Nat.mul_le_mul hplen (Nat.pow_le_pow_right (by omega)
      (Nat.add_le_add_right hpdeg 1))
  · intro v z hv hz hzv hcoord
    have heval := hreval ℂ (Polynomial.aeval θ).toRingHom ν hg_zero
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.aeval_X] at heval
    exact heval.trans (hpeval ![θ, ν] v z hv hz hzv hcoord)

end WeierstrassEllipticZeta

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
    (h_arithmetic : ArithmeticJetData L)
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (ν : ℂ)
    (g : ℤ[X][X]) (hg_monic : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_kernel : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
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
  have hg_zero : g.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 :=
    (hg_kernel g).mpr (dvd_refl g)
  have h_reduced := reduced_arithmetic_jets_of_arithmetic_jets L h_arithmetic θ ν
    g hg_monic hg_degree hg_zero
  exact exists_complex_auxiliary_systems_from_reduced_arithmetic_jets L ω u₁ u₂ h_grid
    h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g hg_monic hg_degree hg_kernel
    h_reduced d hd h_data
