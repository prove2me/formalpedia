-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_bounded_auxiliary_systems
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T09:51:59.877313+00:00
-- url     : https://prove2.me/submissions/6e1af9ab-08c0-40f0-a476-5b8f558ef2ee

import Theorems.Thm_TranscendenceTheory_exists_reduced_bivariate_model
import Theorems.Thm_TranscendenceTheory_bounded_system_of_complex_auxiliary_system
import Theorems.Thm_WeierstrassEllipticZeta_exists_reduced_complex_auxiliary_systems

open WeierstrassEllipticZeta Polynomial Filter
open scoped Polynomial

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (hω_ne : ω ≠ 0) (hω_period : ω ∈ L.lattice)
    (h_linearIndependent : LinearIndependent ℚ ![u₁, u₂, ω])
    (h_intersection : Submodule.span ℤ {u₁, u₂} ⊓ L.lattice = ⊥)
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
    (hν : ∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (Polynomial.aeval θ).toRingHom ν = 0)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_data : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i)) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        Nonempty (TranscendenceTheory.BoundedBivariateSystem θ ν a c N) := by
  obtain ⟨g, hg_monic, hg_degree, hg_kernel, hreduce⟩ :=
    TranscendenceTheory.exists_reduced_bivariate_model θ ν hθ hν
  have h_data_reduced : ∀ i : Fin 18, ∃ p : ℤ[X][X],
      p.natDegree < g.natDegree ∧
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = Polynomial.aeval θ d *
        (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂] i) := by
    intro i
    obtain ⟨p, hp⟩ := h_data i
    obtain ⟨q, ⟨hq_degree, hq_eval⟩, _⟩ := hreduce p
    exact ⟨q, hq_degree, hq_eval.trans hp⟩
  obtain ⟨a, c, ha, hc, hsystems⟩ :=
    exists_reduced_complex_auxiliary_systems L ω u₁ u₂ hω_ne hω_period
      h_linearIndependent h_intersection h_zeta_deriv h_zeta_addition h_wp_addition
      θ hθ ν g hg_monic hg_degree hg_kernel d hd h_data_reduced
  refine ⟨a, c, ha, hc, ?_⟩
  filter_upwards [hsystems] with N hN
  obtain ⟨S, hred⟩ := hN
  exact TranscendenceTheory.bounded_system_of_complex_auxiliary_system θ ν g
    (fun p hp => (hg_kernel p).mp hp) a c N S hred
