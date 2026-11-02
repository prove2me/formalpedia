-- Prove2me | solution 1 for avram_wave5_03_actual_original_expected_full_stieltj_pointwise_upper_bound_448b4247
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:48:58.420402+00:00
-- url     : https://prove2.me/submissions/3c2d9f4e-b3ec-45bd-8640-302b29e6fc9d

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
    (hterminal : (let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : Ω → ℝ≥0 → ℝ := (fun ω t => x + X.X t ω - rightLimit D t ω); let Z : Ω → ℕ → ℝ := (fun ω i => x + X.X (u (i + 1)) ω - rightLimit D (u i) ω); let cash : Ω → ℝ := (fun ω => (∫⁻ s in Icc (0 : ℝ) (u n : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal); let source : Ω → ℝ := (fun ω => ∑ i ∈ Finset.range n, ((E (u (i + 1)) - E (u i)) * V (Y ω (u (i + 1))) + E (u i) * (V (Z ω i) - V (Y ω (u i))))); (∀ (ω : Ω), 0 ≤ V (Y ω (u n)))))
    : (let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))); let Y : Ω → ℝ≥0 → ℝ := (fun ω t => x + X.X t ω - rightLimit D t ω); let Z : Ω → ℕ → ℝ := (fun ω i => x + X.X (u (i + 1)) ω - rightLimit D (u i) ω); let cash : Ω → ℝ := (fun ω => (∫⁻ s in Icc (0 : ℝ) (u n : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal); let source : Ω → ℝ := (fun ω => ∑ i ∈ Finset.range n, ((E (u (i + 1)) - E (u i)) * V (Y ω (u (i + 1))) + E (u i) * (V (Z ω i) - V (Y ω (u i))))); (∀ (ω : Ω), cash ω ≤ V x + source ω)) := by
  dsimp only at hterminal ⊢
  intro ω
  have hgrid :=
    avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
      X x C hC q hq w V hw_cont hw_smooth hw_grad
      hVtop hVfinite D hD ω u n hu hu0 (hPre ω)
  dsimp only at hgrid
  have hterm :
      0 ≤ Real.exp (-(q * (u n : ℝ))) *
        V (x + X.X (u n) ω - rightLimit D (u n) ω) :=
    mul_nonneg (Real.exp_pos _).le (hterminal ω)
  nlinarith only [hgrid, hterm]
