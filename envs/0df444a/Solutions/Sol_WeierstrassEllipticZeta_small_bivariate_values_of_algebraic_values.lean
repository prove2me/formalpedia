-- Prove2me | solution 1 for WeierstrassEllipticZeta.small_bivariate_values_of_algebraic_values
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T11:24:16.652105+00:00
-- url     : https://prove2.me/submissions/81423d79-6397-43a6-9899-a0c3e6079723

import Theorems.Thm_TranscendenceTheory_exists_integral_generator_and_common_denominator
import Theorems.Thm_WeierstrassEllipticZeta_algebraic_auxiliary_values
import Theorems.Thm_WeierstrassEllipticZeta_small_bivariate_values_of_integral_auxiliary_data

open WeierstrassEllipticZeta Polynomial

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
    (h_values : ∀ i, IsAlgebraic (Algebra.adjoin ℚ {θ})
      (theoremOneValues L ω u₁ u₂ i)) :
    ∃ ν : ℂ,
      (∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (Polynomial.aeval θ).toRingHom ν = 0) ∧
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
        ∀ᶠ N : ℕ in Filter.atTop, ∃ P : ℤ[X][X],
          (P.natDegree : ℝ) ≤ A * N ∧
          (∀ j, ((P.coeff j).natDegree : ℝ) ≤ A * N) ∧
          (∀ j k, |((P.coeff j).coeff k : ℝ)| ≤ Real.exp (A * N)) ∧
          P.eval₂ (Polynomial.aeval θ).toRingHom ν ≠ 0 ∧
          ‖P.eval₂ (Polynomial.aeval θ).toRingHom ν‖ ≤
            Real.exp (-c * (N : ℝ) ^ 2 * Real.log N) := by
  have hu₁ : u₁ ∉ L.lattice := by
    intro h
    have hm : u₁ ∈ Submodule.span ℤ {u₁, u₂} ⊓ L.lattice :=
      ⟨Submodule.subset_span (by simp), h⟩
    rw [h_intersection, Submodule.mem_bot] at hm
    exact (h_linearIndependent.ne_zero 0) hm
  have hu₂ : u₂ ∉ L.lattice := by
    intro h
    have hm : u₂ ∈ Submodule.span ℤ {u₁, u₂} ⊓ L.lattice :=
      ⟨Submodule.subset_span (by simp), h⟩
    rw [h_intersection, Submodule.mem_bot] at hm
    exact (h_linearIndependent.ne_zero 1) hm
  have halg := algebraic_auxiliary_values L ω u₁ u₂ θ hu₁ hu₂ h_values
  obtain ⟨ν, hν, d, hd, h_data⟩ :=
    TranscendenceTheory.exists_integral_generator_and_common_denominator θ hθ
      (![L.g₂/4, L.g₃/4, ω, zetaQuasiPeriod L ω, u₁/2, u₂,
        weierstrassZeta L (u₁/2), L.weierstrassP (u₁/2),
        L.derivWeierstrassP (u₁/2), deriv L.derivWeierstrassP (u₁/2),
        L.weierstrassP u₁, L.derivWeierstrassP u₁, deriv L.derivWeierstrassP u₁,
        weierstrassZeta L u₁, L.weierstrassP u₂, L.derivWeierstrassP u₂,
        deriv L.derivWeierstrassP u₂, weierstrassZeta L u₂]) halg
  refine ⟨ν, hν, ?_⟩
  exact small_bivariate_values_of_integral_auxiliary_data
    L ω u₁ u₂ hω_ne hω_period h_linearIndependent h_intersection
    h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν hν d hd h_data
