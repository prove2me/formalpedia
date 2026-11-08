-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.tendsto_charFun_marginal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:29:13.781461+00:00
-- url     : https://prove2.me/submissions/26005001-f7c8-4f89-97ca-8af004c21de0

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (t₀ : ℝ≥0) (ξ : E) :
    Tendsto (fun t => charFun (μ.map (X t)) ξ)
      (𝓝[≥] t₀) (𝓝 (charFun (μ.map (X t₀)) ξ)) := by
  -- Rewrite charFun as integral over base measure μ via change of variables
  set F : ℝ≥0 → Ω → ℂ := fun t ω =>
    cexp (Complex.ofReal (@inner ℝ E _ (X t ω) ξ) * I) with hF_def
  have hcov : ∀ t, charFun (μ.map (X t)) ξ = ∫ ω, F t ω ∂μ := by
    intro t; rw [hF_def, charFun_apply, integral_map (hX t).aemeasurable]
    exact (by fun_prop : AEStronglyMeasurable (fun x => cexp (↑(@inner ℝ E _ x ξ) * I))
      (μ.map (X t)))
  -- Suffices to show convergence of the integrals over μ
  suffices Tendsto (fun t => ∫ ω, F t ω ∂μ) (𝓝[≥] t₀) (𝓝 (∫ ω, F t₀ ω ∂μ)) by
    have h1 : (fun t => charFun (μ.map (X t)) ξ) = fun t => ∫ ω, F t ω ∂μ :=
      funext hcov
    rw [h1, hcov t₀]; exact this
  -- Apply DCT with constant bound 1
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
  -- AEStronglyMeasurable for each t
  · apply Eventually.of_forall; intro t
    have : Measurable (fun ω => cexp (↑(@inner ℝ E _ (X t ω) ξ) * I)) := by fun_prop
    exact this.aestronglyMeasurable
  -- Norm bound ≤ 1
  · apply Eventually.of_forall; intro t
    apply Eventually.of_forall; intro ω
    simp only [hF_def, norm_exp_ofReal_mul_I]; exact le_refl _
  -- Integrability of bound
  · exact integrable_const 1
  -- Pointwise convergence from càdlàg
  · filter_upwards [h.cadlag_ae] with ω hω
    simp only [hF_def]
    -- X t ω → X t₀ ω as t → t₀+ by càdlàg
    have hXtend : Tendsto (fun t => X t ω) (𝓝[≥] t₀) (𝓝 (X t₀ ω)) :=
      (hω t₀).1
    -- (X t ω, ξ) → (X t₀ ω, ξ) in the product topology
    have hPtend : Tendsto (fun t => (X t ω, ξ)) (𝓝[≥] t₀) (𝓝 (X t₀ ω, ξ)) :=
      Filter.Tendsto.prodMk_nhds hXtend tendsto_const_nhds
    -- ⟪X t ω, ξ⟫ → ⟪X t₀ ω, ξ⟫ by continuity of inner product
    have hItend : Tendsto (fun t => @inner ℝ E _ (X t ω) ξ) (𝓝[≥] t₀)
        (𝓝 (@inner ℝ E _ (X t₀ ω) ξ)) :=
      (continuous_inner.tendsto _).comp hPtend
    -- exp(ofReal(⟪·, ξ⟫) * I) is continuous
    exact (((Complex.continuous_ofReal.tendsto _).comp hItend).mul
      tendsto_const_nhds).cexp
