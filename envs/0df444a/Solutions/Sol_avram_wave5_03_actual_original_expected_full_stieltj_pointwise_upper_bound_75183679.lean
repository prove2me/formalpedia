-- Prove2me | solution 1 for avram_wave5_03_actual_original_expected_full_stieltj_pointwise_upper_bound_75183679
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:47:39.483644+00:00
-- url     : https://prove2.me/submissions/f4680333-2c32-4ba4-9099-2ca9a2f7d046

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ ω (i : ℕ), i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (hCashInt : Integrable (fun ω => (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (hSourceInt : Integrable (fun ω =>
      ∑ i ∈ Finset.range n,
          ((Real.exp (-(q * (u (i + 1) : ℝ))) -
              Real.exp (-(q * (u i : ℝ)))) *
              V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) +
            Real.exp (-(q * (u i : ℝ))) *
              (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
                V (x + X.X (u i) ω - rightLimit D (u i) ω)))) P) 
    (hcash : (let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : Ω → ℝ≥0 → ℝ := (fun ω t => x + X.X t ω - rightLimit D t ω); let Z : Ω → ℕ → ℝ := (fun ω i => x + X.X (u (i + 1)) ω - rightLimit D (u i) ω); let cash : Ω → ℝ := (fun ω => (∫⁻ s in Icc (0 : ℝ) (u n : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal); let source : Ω → ℝ := (fun ω => ∑ i ∈ Finset.range n, ((E (u (i + 1)) - E (u i)) * V (Y ω (u (i + 1))) + E (u i) * (V (Z ω i) - V (Y ω (u i))))); Integrable cash P))
    (hsource : (let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : Ω → ℝ≥0 → ℝ := (fun ω t => x + X.X t ω - rightLimit D t ω); let Z : Ω → ℕ → ℝ := (fun ω i => x + X.X (u (i + 1)) ω - rightLimit D (u i) ω); let cash : Ω → ℝ := (fun ω => (∫⁻ s in Icc (0 : ℝ) (u n : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal); let source : Ω → ℝ := (fun ω => ∑ i ∈ Finset.range n, ((E (u (i + 1)) - E (u i)) * V (Y ω (u (i + 1))) + E (u i) * (V (Z ω i) - V (Y ω (u i))))); Integrable source P))
    : (let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : Ω → ℝ≥0 → ℝ := (fun ω t => x + X.X t ω - rightLimit D t ω); let Z : Ω → ℕ → ℝ := (fun ω i => x + X.X (u (i + 1)) ω - rightLimit D (u i) ω); let cash : Ω → ℝ := (fun ω => (∫⁻ s in Icc (0 : ℝ) (u n : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal); let source : Ω → ℝ := (fun ω => ∑ i ∈ Finset.range n, ((E (u (i + 1)) - E (u i)) * V (Y ω (u (i + 1))) + E (u i) * (V (Z ω i) - V (Y ω (u i))))); (∀ (ω : Ω), 0 ≤ V (Y ω (u n)))) := by
  change ∀ ω : Ω, 0 ≤ V (x + X.X (u n) ω - rightLimit D (u n) ω)
  intro ω
  let z : ℝ := x + X.X (u n) ω - rightLimit D (u n) ω
  have hw : 0 ≤ w z :=
    avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
      X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hx hxc D hD ω (u n)
  have hcap : ENNReal.ofReal z ≤ C :=
    capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω (u n)
  change 0 ≤ V z
  by_cases hz0 : 0 ≤ z
  · have heq :=
      avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap
        C hC w V hVtop hVfinite z hz0 hcap
    rw [heq]
    exact hw
  · have hzneg : z < 0 := lt_of_not_ge hz0
    by_cases htop : C = ⊤
    · rw [hVtop htop]
      exact hw
    · have hzcap : z ≤ C.toReal :=
        (le_of_lt hzneg).trans ENNReal.toReal_nonneg
      rw [hVfinite htop z, if_pos hzcap]
      exact hw
