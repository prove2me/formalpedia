-- Prove2me | solution 1 for WeierstrassEllipticZeta.exists_complex_auxiliary_systems_from_grid_parameters
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T15:27:56.525457+00:00
-- url     : https://prove2.me/submissions/fdf747aa-824c-4e12-8bea-7cb5ce29ed54

import Theorems.Thm_WeierstrassEllipticZeta_exists_complex_auxiliary_systems_from_interpolation_decay
import Theorems.Thm_TranscendenceTheory_finite_zeros_exponential_derivative_bound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_WeierstrassEllipticZeta_InterpolationDecay

open Filter Metric Set
open scoped Topology

namespace WeierstrassEllipticZeta

private theorem auxiliary_grid_decay_data (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂) :
    AuxiliaryGridDecayData ω u₁ u₂ := by
  intro B K hB hK
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hscale := (tendsto_rpow_atTop (by norm_num : 0 < (1 / 72 : ℝ))).comp hn
  have hdecay := TranscendenceTheory.finite_zeros_exponential_derivative_bound
    (1 / 512) (1 / 72) B K (by norm_num) (by norm_num) hB hK
  filter_upwards [h_parameters 1 (by norm_num), hdecay,
    hn.eventually (eventually_ge_atTop (2 : ℝ)), hscale.eventually_ge_atTop 2]
    with N hN hdecay hN2 hscale
  rcases hN with ⟨hm, hl, hs, hq, hsq, hgap, hcount, hupper,
    hmlog, hls, hR, hr, hlarge, hratio, hgrowth⟩
  dsimp only
  let r : ℝ := 4 * auxiliaryS3 N * (‖u₁‖ + ‖u₂‖ + ‖ω‖ + 1)
  let Γ := shiftedAuxiliaryGrid u₁ u₂ ω ![auxiliaryS N, auxiliaryS N, auxiliaryS3 N]
  change 0 < r at hr
  change 2 * r / auxiliaryRadius N ≤ (N : ℝ) ^ (-1 / 36 : ℝ) at hratio
  have hN0 : (0 : ℝ) < N := by linarith only [hN2]
  have hlog : 0 < Real.log N := Real.log_pos (by linarith only [hN2])
  have hR0 : 0 < auxiliaryRadius N := by linarith only [hR]
  have hscale' : 2 * (N : ℝ) ^ (-1 / 36 : ℝ) ≤ (N : ℝ) ^ (-1 / 72 : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 72 : ℝ) * (N : ℝ) ^ (-1 / 36 : ℝ) :=
        mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = _ := by rw [← Real.rpow_add hN0]; norm_num
  have hratio' : 2 * (2 * r) / auxiliaryRadius N ≤ (N : ℝ) ^ (-(1 / 72 : ℝ)) := by
    calc
      _ = 2 * (2 * r / auxiliaryRadius N) := by ring
      _ ≤ 2 * (N : ℝ) ^ (-1 / 36 : ℝ) := mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ ≤ _ := by simpa only [neg_div] using hscale'
  have hrR : 2 * r < auxiliaryRadius N := by
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg
      (by linarith only [hN2] : (1 : ℝ) < N) (by norm_num : -(1 / 72 : ℝ) < 0)
    have h := (div_lt_one hR0).mp (hratio'.trans_lt hlt)
    linarith only [h, hr]
  have hnodes : ∀ z ∈ Γ, ‖z‖ ≤ r := by
    intro z hz
    have hzbound := h_grid.shifted_grid_radius _ z hz
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hzbound
    have hsq' : (auxiliaryS N : ℝ) ≤ auxiliaryS3 N := by exact_mod_cast hsq
    have hq' : (1 : ℝ) ≤ auxiliaryS3 N := by exact_mod_cast hq
    have hu1 := mul_le_mul_of_nonneg_right hsq' (norm_nonneg u₁)
    have hu2 := mul_le_mul_of_nonneg_right hsq' (norm_nonneg u₂)
    have hu3 := mul_le_mul_of_nonneg_right hq' (norm_nonneg u₁)
    dsimp only [r]
    nlinarith only [hzbound, hu1, hu2, hu3, hq',
      mul_nonneg (Nat.cast_nonneg (auxiliaryS3 N)) (norm_nonneg u₁),
      mul_nonneg (Nat.cast_nonneg (auxiliaryS3 N)) (norm_nonneg u₂),
      mul_nonneg (Nat.cast_nonneg (auxiliaryS3 N)) (norm_nonneg ω)]
  intro v hv f G ψ hG hf hψ hGf hjet houter w hw n hn_bound
  have hzero : ∀ x ∈ Γ.image (fun z => z - v),
      ∀ j < auxiliaryL0 N + 1, iteratedDeriv j G x = 0 := by
    intro x hx
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hG x trivial)).1
    have hfT := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf x hx)).2
      (hjet x hx)
    rw [analyticOrderAt_congr (hGf x hx)]
    change (auxiliaryL0 N + 1 : ℕ∞) ≤ analyticOrderAt (ψ * f) x
    rw [analyticOrderAt_mul (hψ x hx) (hf x hx)]
    exact hfT.trans le_add_self
  have hcard : (Γ.image (fun z => z - v)).card = Γ.card :=
    Finset.card_image_of_injective _ (by intro a b h; exact sub_left_inj.mp h)
  have hsum : (∑ x ∈ Γ.image (fun z => z - v), (auxiliaryL0 N + 1)) =
      Γ.card * (auxiliaryL0 N + 1) := by
    simp only [Finset.sum_const, nsmul_eq_mul, hcard, Nat.cast_id]
  have hcount' : (1 / 512 : ℝ) * (N : ℝ) ^ 2 ≤
      (∑ x ∈ Γ.image (fun z => z - v), (auxiliaryL0 N + 1) : ℕ) := by
    rw [hsum]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm, div_eq_mul_inv,
      one_mul] using hcount
  have hnodes' : ∀ z ∈ Γ.image (fun x => x - v), ‖z‖ ≤ 2 * r := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    calc
      ‖x - v‖ ≤ ‖x‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ r + r := add_le_add (hnodes x hx) hv
      _ = 2 * r := by ring
  have hn' : (n : ℝ) ≤ K * ((N : ℝ) / Real.log N) := by
    apply hn_bound.trans
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) hK.le
  have hsmall := hdecay G hG (Γ.image (fun z => z - v))
    (fun _ => auxiliaryL0 N + 1) hzero (2 * r) (auxiliaryRadius N)
    (by positivity) hrR hnodes' hcount' hratio' houter w hw n hn'
  have hexponent : -((1 / 512 : ℝ) * (1 / 72) / 2) * (N : ℝ) ^ 2 * Real.log N =
      -(N : ℝ) ^ 2 * Real.log N / 73728 := by ring
  rw [hexponent] at hsmall
  exact ⟨hsmall.1, hsmall.2 f ψ⟩

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta
open scoped Polynomial

theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_parameters : AuxiliaryGridParameterData L ω u₁ u₂)
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
  have h_decay := auxiliary_grid_decay_data L ω u₁ u₂ h_grid h_parameters
  exact exists_complex_auxiliary_systems_from_interpolation_decay L ω u₁ u₂ h_grid h_parameters h_decay
    h_zeta_deriv h_zeta_addition h_wp_addition θ hθ ν g hg_monic hg_degree hg_kernel
    h_jet_systems h_interpolation h_regularization h_cleared_entire d hd h_period_jets h_data
