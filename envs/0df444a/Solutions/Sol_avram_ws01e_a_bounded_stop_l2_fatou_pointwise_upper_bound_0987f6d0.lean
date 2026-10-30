-- Prove2me | solution 1 for avram_ws01e_a_bounded_stop_l2_fatou_pointwise_upper_bound_0987f6d0
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T06:47:58.082999+00:00
-- url     : https://prove2.me/submissions/a8efdec6-7cfb-48bc-b717-652b91dd31bd

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_finite_grid_stop_likelihood_l2_lintegral_bound

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T H : ℝ≥0) (τ : Ω → ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0)
    (hgrid : ∀ n ω, τn n ω ∈ grid n)
    (hT : ∀ (n : ℕ) (s : ℝ≥0), s ∈ grid n → s ≤ T)
    (hstop : ∀ (n : ℕ) (s : ℝ≥0), s ∈ grid n →
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (hbound : ∀ n ω, τn n ω ≤ H)
    (hlim : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hfmeas : (let f : ℕ → Ω → ℝ≥0∞ := (fun n ω => ENNReal.ofReal ((Real.exp (θ * X.X (τn n ω) ω - (τn n ω : ℝ) * X.ψ θ)) ^ 2)); let C : ℝ≥0∞ := (ENNReal.ofReal (Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|))); ∀ n, Measurable (f n)))
    (hpow : (let f : ℕ → Ω → ℝ≥0∞ := (fun n ω => ENNReal.ofReal ((Real.exp (θ * X.X (τn n ω) ω - (τn n ω : ℝ) * X.ψ θ)) ^ 2)); let C : ℝ≥0∞ := (ENNReal.ofReal (Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|))); ∀ n ω,
      (Real.exp (θ * X.X (τn n ω) ω -
        (τn n ω : ℝ) * X.ψ θ)) ^ 2 =
      Real.exp ((2 * θ) * X.X (τn n ω) ω -
        2 * (τn n ω : ℝ) * X.ψ θ)))
    : (let f : ℕ → Ω → ℝ≥0∞ := (fun n ω => ENNReal.ofReal ((Real.exp (θ * X.X (τn n ω) ω - (τn n ω : ℝ) * X.ψ θ)) ^ 2)); let C : ℝ≥0∞ := (ENNReal.ofReal (Real.exp ((H : ℝ) * |X.ψ (2 * θ) - 2 * X.ψ θ|))); ∀ n, (∫⁻ ω, f n ω ∂P) ≤ C) := by
  intro f C n
  have hp : ∀ n ω, (Real.exp (θ * X.X (τn n ω) ω - (τn n ω : ℝ) * X.ψ θ)) ^ 2 =
      Real.exp ((2 * θ) * X.X (τn n ω) ω - 2 * (τn n ω : ℝ) * X.ψ θ) := hpow
  have h := esscher_finite_grid_stop_likelihood_l2_lintegral_bound X θ hθ T H (τn n) (grid n)
    (hgrid n) (hT n) (hstop n) (hbound n)
  have e : (∫⁻ ω, f n ω ∂P) = ∫⁻ ω, ENNReal.ofReal
      (Real.exp ((2 * θ) * X.X (τn n ω) ω - 2 * (τn n ω : ℝ) * X.ψ θ)) ∂P := by
    apply lintegral_congr
    intro ω
    show ENNReal.ofReal _ = _
    rw [hp n ω]
  rw [e]
  exact h
