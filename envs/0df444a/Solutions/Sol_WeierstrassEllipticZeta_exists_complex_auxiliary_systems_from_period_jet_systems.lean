-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_period_jet_systems
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T15:03:05.187124+00:00
-- url     : https://prove2.me/submissions/7bd1fd2e-83b9-4052-a04a-6bd634617703

import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_grid_parameters
import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_parameter_estimates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open Filter

namespace WeierstrassEllipticZeta

private theorem auxiliary_grid_parameter_data (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂) :
    AuxiliaryGridParameterData L ω u₁ u₂ := by
  intro B hB
  let U := ‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1
  have hU : 0 < U := by dsimp [U]; positivity
  have hA : 0 < B + U := add_pos hB hU
  filter_upwards [auxiliary_parameter_estimates (B + U) hA] with N hN
  rcases hN with ⟨hm, hl, hs, hq, hsq, hgap, hlo, hhi, hlog, hls, hR, hrad, hgrowth⟩
  dsimp only
  have hcard : (shiftedAuxiliaryGrid u₁ u₂ ω
      ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N]).card =
      auxiliaryS N ^ 2 * auxiliaryS3 N := by
    rw [h_grid.card_shifted_grid]
    simp [Fin.prod_univ_succ, pow_two, mul_assoc]
  rw [hcard]
  have hgap' : 8 * ((auxiliaryL0 N + 1) * (auxiliaryS N ^ 2 * auxiliaryS3 N)) ≤
      (auxiliaryL0 N + 1) * (auxiliaryL N + 1) ^ 2 := by simpa [mul_assoc] using hgap
  have hlo' : (N : ℝ) ^ 2 / 512 ≤
      (auxiliaryL0 N + 1 : ℝ) * ↑(auxiliaryS N ^ 2 * auxiliaryS3 N) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc] using hlo
  have hhi' : (auxiliaryL0 N + 1 : ℝ) * ↑(auxiliaryS N ^ 2 * auxiliaryS3 N) ≤
      (N : ℝ) ^ 2 / 32 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc] using hhi
  refine ⟨hm, hl, hs, hq, hsq, hgap', hlo', hhi', hlog, hls, hR, ?_, ?_, ?_, ?_⟩
  · change 0 < 4 * (auxiliaryS3 N : ℝ) * U
    have : 0 < (auxiliaryS3 N : ℝ) := by exact_mod_cast (by omega : 0 < auxiliaryS3 N)
    positivity
  · intro z hz
    refine ⟨h_grid.shifted_grid_regular _ z hz, ?_⟩
    have hzbound := h_grid.shifted_grid_radius _ z hz
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Nat.cast_mul, Nat.cast_ofNat] at hzbound
    have hsq' : (auxiliaryS N : ℝ) ≤ auxiliaryS3 N := by exact_mod_cast hsq
    have hq' : (1 : ℝ) ≤ auxiliaryS3 N := by exact_mod_cast hq
    have hu1 := mul_le_mul_of_nonneg_right hsq' (norm_nonneg u₁)
    have hu2 := mul_le_mul_of_nonneg_right hsq' (norm_nonneg u₂)
    have hu3 := mul_le_mul_of_nonneg_right hq' (norm_nonneg u₁)
    nlinarith only [hzbound, hu1, hu2, hu3, hq',
      mul_nonneg (Nat.cast_nonneg (auxiliaryS3 N)) (norm_nonneg u₁),
      mul_nonneg (Nat.cast_nonneg (auxiliaryS3 N)) (norm_nonneg u₂),
      mul_nonneg (Nat.cast_nonneg (auxiliaryS3 N)) (norm_nonneg ω)]
  · change 2 * (4 * (auxiliaryS3 N : ℝ) * U) / auxiliaryRadius N ≤ _
    calc
      _ ≤ 8 * (B + U) * auxiliaryS3 N / auxiliaryRadius N := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        nlinarith [mul_nonneg hB.le (Nat.cast_nonneg (auxiliaryS3 N))]
      _ ≤ _ := hrad
  · calc
      B * auxiliaryL N * auxiliaryRadius N ^ 2 ≤
          (B + U) * auxiliaryL N * auxiliaryRadius N ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        linarith
      _ ≤ _ := hgrowth

end WeierstrassEllipticZeta

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
    (θ : ℂ) (hθ : Transcendental ℚ θ)
    (ν : ℂ)
    (g : ℤ[X][X]) (hg_monic : g.Monic) (hg_degree : 0 < g.natDegree)
    (hg_kernel : ∀ p : ℤ[X][X],
      p.eval₂ (Polynomial.aeval θ).toRingHom ν = 0 ↔ g ∣ p)
    (h_jet_systems : ReducedArithmeticJetSystemData L θ ν g)
    (h_interpolation : AuxiliaryGridInterpolationData ω u₁ u₂)
    (h_regularization : EllipticRegularizationData L ω u₁ u₂)
    (h_cleared_entire : ClearedAdditionEntireData L ω u₁ u₂)
    (d : ℤ[X]) (hd : Polynomial.aeval θ d ≠ 0)
    (h_period_jets : PeriodArithmeticJetSystemData L ω (u₁ / 2) θ ν g d)
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
  have h_parameters := auxiliary_grid_parameter_data L ω u₁ u₂ h_grid
  exact exists_complex_auxiliary_systems_from_grid_parameters L ω u₁ u₂ h_grid h_parameters
    h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g hg_monic hg_degree hg_kernel
    h_jet_systems h_interpolation h_regularization h_cleared_entire d hd h_period_jets h_data
