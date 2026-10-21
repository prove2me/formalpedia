-- Prove2me | solution 1 for PoSShares.Stability.eq_A31
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:36:51.681727+00:00
-- url     : https://prove2.me/submissions/694ec303-e610-4ed4-8f2e-792895b2c2c3

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (π₁ ε : ℝ) (X : Ω → ℝ) (hπ₁ : π₁ ∈ Set.Ioo (0 : ℝ) 1) (hX : Measurable X)
    (hX01 : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) (hmean : ∫ ω, X ω ∂μ = π₁)
    (hvar : variance X μ = π₁ * (1 - π₁))
    (hε : ε ∈ Set.Ioo (0 : ℝ) (Real.sqrt (π₁ * (1 - π₁)))) :
    (π₁ * (1 - π₁) - ε ^ 2) / (1 - ε ^ 2) ≤ μ.real {ω | ε < |X ω - π₁|} ∧
      0 < (π₁ * (1 - π₁) - ε ^ 2) / (1 - ε ^ 2) := by
  obtain ⟨h0, h1⟩ := hπ₁
  obtain ⟨he0, he1⟩ := hε
  have hv : 0 < π₁ * (1 - π₁) := mul_pos h0 (by linarith)
  have hv4 : π₁ * (1 - π₁) ≤ 1 / 4 := by nlinarith [sq_nonneg (π₁ - 1/2)]
  have hε2 : ε ^ 2 < π₁ * (1 - π₁) := by
    have := Real.sq_sqrt hv.le
    nlinarith
  have hden : 0 < 1 - ε ^ 2 := by linarith
  have hpos : 0 < (π₁ * (1 - π₁) - ε ^ 2) / (1 - ε ^ 2) :=
    div_pos (by linarith) hden
  refine ⟨?_, hpos⟩
  set A : Set Ω := {ω | ε < |X ω - π₁|} with hA
  have hAm : MeasurableSet A :=
    measurableSet_lt measurable_const ((hX.sub measurable_const).abs)
  have hmeanX : μ[X] = π₁ := hmean
  have hvi : variance X μ = ∫ ω, (X ω - π₁) ^ 2 ∂μ := by
    rw [variance_eq_integral hX.aemeasurable, hmeanX]
  -- pointwise bound
  have hpt : ∀ᵐ ω ∂μ, (X ω - π₁) ^ 2 ≤ ε ^ 2 + (1 - ε ^ 2) * A.indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hX01] with ω hω
    obtain ⟨hω0, hω1⟩ := hω
    by_cases hm : ω ∈ A
    · rw [Set.indicator_of_mem hm]
      have : (X ω - π₁) ^ 2 ≤ 1 := by nlinarith
      linarith
    · rw [Set.indicator_of_notMem hm]
      have : |X ω - π₁| ≤ ε := not_lt.mp hm
      have h2 : (X ω - π₁) ^ 2 ≤ ε ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      linarith
  have hint1 : Integrable (fun ω => (X ω - π₁) ^ 2) μ := by
    have hb : ∀ᵐ ω ∂μ, ‖(X ω - π₁) ^ 2‖ ≤ 1 := by
      filter_upwards [hX01] with ω hω
      obtain ⟨hω0, hω1⟩ := hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith
    exact Integrable.of_bound ((hX.sub measurable_const).pow_const 2).aestronglyMeasurable 1 hb
  have hind : Integrable (A.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hAm
  have hint2 : Integrable (fun ω => ε ^ 2 + (1 - ε ^ 2) * A.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const _).add (hind.const_mul _)
  have hle := integral_mono_ae hint1 hint2 hpt
  have hcalc : ∫ ω, (ε ^ 2 + (1 - ε ^ 2) * A.indicator (fun _ => (1 : ℝ)) ω) ∂μ
      = ε ^ 2 + (1 - ε ^ 2) * μ.real A := by
    rw [integral_add (integrable_const _) (hind.const_mul _), integral_const_mul,
      integral_indicator hAm]
    simp
  rw [← hvi, hvar] at hle
  rw [hcalc] at hle
  rw [div_le_iff₀ hden]
  nlinarith
