-- Prove2me | solution 1 for cofinal_ito_to_five_identity_57c30a1d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:00:27.508887+00:00
-- url     : https://prove2.me/submissions/007c909c-e198-46fa-8ea2-2a27b5b8d81a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_cash_nonnegative_from_dividend_measure
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_cofinal_clock_payoff_eventually_exact
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_local_fatou_to_original_five_witness
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (n : ℕ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ ω, (⨆ k : ℕ, S k ω) = ⊤)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (τk : ℕ → Ω → ℝ≥0)
    (hτk : ∀ k ω, τk k ω =
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal)
    (W Cash Term : Ω → ℝ)
    (Wk Cashk Termk : ℕ → Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hWk : ∀ k ω, Wk k ω =
      if τk k ω = 0 ∨ (τk k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τk k ω) ω - rightLimit D (τk k ω) ω
      else riskProcess X x D (τk k ω) ω)
    (hCashk : ∀ k ω, Cashk k ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τk k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    (hTermk : ∀ k ω, Termk k ω =
      Real.exp (-(q * (τk k ω : ℝ))) * w (Wk k ω))
    (hFmeas : ∀ k, Measurable (fun ω => Termk k ω + Cashk k ω))
    (hFint : ∀ k, Integrable (fun ω => Termk k ω + Cashk k ω) P)
    (hBudget : ∀ k, (∫ ω, Termk k ω + Cashk k ω ∂P) ≤ w x) 
    (hTermNN : ∀ ω, 0 ≤ Term ω)
    (hCashNN : ∀ ω, 0 ≤ Cash ω)
    (hFNN : ∀ k, 0 ≤ᵐ[P] (fun ω => Termk k ω + Cashk k ω))
    (hb : 0 ≤ w x)
    : ∀ ω, Tendsto
      (fun k => ENNReal.ofReal (Termk k ω + Cashk k ω)) atTop
      (𝓝 (ENNReal.ofReal (Term ω + Cash ω))) := by
    intro ω
    obtain ⟨K, hK⟩ :=
      avram_p4_f4_original_cofinal_clock_payoff_eventually_exact
        X x C D hD q n S hSmono hSsup τ hτ τk hτk
        W Cash Term Wk Cashk Termk hW hCash w hTerm hWk hCashk hTermk ω
    have he : (fun k => ENNReal.ofReal (Termk k ω + Cashk k ω))
        =ᶠ[atTop] (fun _ => ENNReal.ofReal (Term ω + Cash ω)) := by
      filter_upwards [eventually_ge_atTop K] with k hk
      obtain ⟨_, _, hkC, hkT⟩ := hK k hk
      simp [hkC, hkT]
    exact (tendsto_congr' he).2 tendsto_const_nhds
end
