-- Prove2me | solution 1 for RiskControl.Optimal.setdiff_size_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:53:08.095997+00:00
-- url     : https://prove2.me/submissions/321d35f0-2b50-4749-b01d-6615b81b90ce

import Mathlib
import Definitions.Def_RiskControl_Optimal_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open RiskControl.Optimal

theorem solution {𝒳 𝒴 𝒵 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace 𝒵]
    (P : Measure (𝒳 × 𝒴)) (μ : Measure 𝒵)
    (ℓ : 𝒴 → 𝒵 → ℝ≥0) (hℓ : Measurable (Function.uncurry ℓ))
    (κ : Kernel 𝒳 𝒴) [IsMarkovKernel κ]
    (lam : ℝ) (hlam : lam < 0)
    (T' : 𝒳 → Set 𝒵) (hT' : MeasurableSet {q : 𝒳 × 𝒵 | q.2 ∈ T' q.1})
    (h5 : ∫⁻ x, ∫⁻ z in thresholdSet κ ℓ lam x \ T' x, condLoss κ ℓ x z ∂μ ∂P.fst
      ≤ ∫⁻ x, ∫⁻ z in T' x \ thresholdSet κ ℓ lam x, condLoss κ ℓ x z ∂μ ∂P.fst) :
    ∫⁻ x, μ (thresholdSet κ ℓ lam x \ T' x) ∂P.fst
      ≤ ∫⁻ x, μ (T' x \ thresholdSet κ ℓ lam x) ∂P.fst := by
  set c : ℝ≥0∞ := ENNReal.ofReal (-lam) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; simp [hlam]
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hT'x : ∀ x, MeasurableSet (T' x) := fun x => measurable_prodMk_left hT'
  have hcl : ∀ x, Measurable (fun z => condLoss κ ℓ x z) := by
    intro x
    have h1 : Measurable (fun p : 𝒴 × 𝒵 => (ℓ p.1 p.2 : ℝ≥0∞)) :=
      measurable_coe_nnreal_ennreal.comp hℓ
    exact Measurable.lintegral_prod_left' (μ := κ x) h1
  have hTl : ∀ x, MeasurableSet (thresholdSet κ ℓ lam x) := by
    intro x
    exact measurableSet_le measurable_const (hcl x)
  have lower : ∀ x, c * μ (thresholdSet κ ℓ lam x \ T' x) ≤
      ∫⁻ z in thresholdSet κ ℓ lam x \ T' x, condLoss κ ℓ x z ∂μ := by
    intro x
    have hs : MeasurableSet (thresholdSet κ ℓ lam x \ T' x) := (hTl x).diff (hT'x x)
    calc c * μ (thresholdSet κ ℓ lam x \ T' x)
        = ∫⁻ z in thresholdSet κ ℓ lam x \ T' x, c ∂μ := by rw [setLIntegral_const, mul_comm]
      _ ≤ _ := setLIntegral_mono' hs (fun z hz => hz.1)
  have upper : ∀ x, ∫⁻ z in T' x \ thresholdSet κ ℓ lam x, condLoss κ ℓ x z ∂μ ≤
      c * μ (T' x \ thresholdSet κ ℓ lam x) := by
    intro x
    have hs : MeasurableSet (T' x \ thresholdSet κ ℓ lam x) := (hT'x x).diff (hTl x)
    calc ∫⁻ z in T' x \ thresholdSet κ ℓ lam x, condLoss κ ℓ x z ∂μ
        ≤ ∫⁻ z in T' x \ thresholdSet κ ℓ lam x, c ∂μ := by
          apply setLIntegral_mono' hs
          intro z hz
          have : ¬ (c ≤ condLoss κ ℓ x z) := hz.2
          exact (not_le.mp this).le
      _ = c * μ (T' x \ thresholdSet κ ℓ lam x) := by rw [setLIntegral_const, mul_comm]
  have h1 : c * ∫⁻ x, μ (thresholdSet κ ℓ lam x \ T' x) ∂P.fst ≤
      c * ∫⁻ x, μ (T' x \ thresholdSet κ ℓ lam x) ∂P.fst := by
    rw [← lintegral_const_mul' c _ hctop, ← lintegral_const_mul' c _ hctop]
    calc ∫⁻ x, c * μ (thresholdSet κ ℓ lam x \ T' x) ∂P.fst
        ≤ ∫⁻ x, ∫⁻ z in thresholdSet κ ℓ lam x \ T' x, condLoss κ ℓ x z ∂μ ∂P.fst :=
          lintegral_mono lower
      _ ≤ ∫⁻ x, ∫⁻ z in T' x \ thresholdSet κ ℓ lam x, condLoss κ ℓ x z ∂μ ∂P.fst := h5
      _ ≤ _ := lintegral_mono upper
  exact (ENNReal.mul_le_mul_iff_right hc0 hctop).mp h1
