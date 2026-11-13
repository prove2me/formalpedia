-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.cavity_affine_transport
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:26:03.333465+00:00
-- url     : https://prove2.me/submissions/f49b0462-0877-49be-a6f0-b4b514bf48ba

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option autoImplicit false
open scoped Classical
open MeasureTheory Set
open ZeroFreeRRG.Hardcore

private def affineMessage (m : Model) (r : m.Spin → ℝ) (c : ℝ) (μ : m.Spin → ℝ) : m.Spin → ℝ :=
  fun i => (1-c)*r i + c*μ i

private theorem affineMessage_cont (m : Model) (r : m.Spin → ℝ) (c : ℝ) :
    Continuous (affineMessage m r c) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_const.mul (continuous_apply i))

/-- Affinely contracting cavity messages transports their barycenter. -/
theorem cavity_affine (m : Model) (t t' : ℝ) (ν : ProbabilityMeasure (m.Spin → ℝ))
    (hν : ν ∈ cavityLaws m t) (r : m.Spin → ℝ) (hr : r ∈ stdSimplex ℝ m.Spin)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hmean : ∀ i, m.pi t' i = (1-c)*r i+c*m.pi t i) :
    ν.map (affineMessage_cont m r c).measurable.aemeasurable ∈ cavityLaws m t' := by
  let f := affineMessage m r c
  have hf : Measurable f := (affineMessage_cont m r c).measurable
  have hae : ∀ᵐ μ ∂(ν : Measure (m.Spin → ℝ)), μ ∈ stdSimplex ℝ m.Spin := by
    apply ae_iff.mpr
    exact hν.1
  have hfm : ∀ᵐ μ ∂(ν : Measure (m.Spin → ℝ)), f μ ∈ stdSimplex ℝ m.Spin := by
    filter_upwards [hae] with μ hμ
    have hh := (convex_stdSimplex ℝ m.Spin) hr hμ (show 0 ≤ 1-c by linarith) hc0 (by ring : 1-c+c=1)
    change (fun i => (1-c)*r i+c*μ i) ∈ stdSimplex ℝ m.Spin
    simpa [Pi.add_def,Pi.smul_def,smul_eq_mul] using hh
  constructor
  · apply ae_iff.mp
    apply (ae_map_iff hf.aemeasurable (isClosed_stdSimplex ℝ m.Spin).measurableSet).2
    exact hfm
  · intro i
    have hint : Integrable (fun μ : m.Spin → ℝ => μ i) (ν : Measure (m.Spin → ℝ)) := by
      apply Integrable.of_bound (continuous_apply i).aestronglyMeasurable 1
      filter_upwards [hae] with μ hμ
      have hh := mem_Icc_of_mem_stdSimplex hμ i
      simpa [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2
    have hmap : ∫ μ : m.Spin → ℝ, μ i ∂((ν.map (affineMessage_cont m r c).measurable.aemeasurable : ProbabilityMeasure (m.Spin → ℝ)) : Measure (m.Spin → ℝ)) =
        ∫ μ : m.Spin → ℝ, f μ i ∂(ν : Measure (m.Spin → ℝ)) := by
      exact integral_map hf.aemeasurable (continuous_apply i).aestronglyMeasurable
    rw [hmap]
    change (∫ μ : m.Spin → ℝ, ((1-c)*r i + c*μ i) ∂(ν : Measure (m.Spin → ℝ))) = m.pi t' i
    rw [integral_add (integrable_const _) (hint.const_mul c),integral_const,integral_const_mul,hν.2 i]
    simp only [probReal_univ, one_smul]
    exact (hmean i).symm

theorem solution (m : Model) (t t' : ℝ) (ν : ProbabilityMeasure (m.Spin → ℝ))
    (hν : ν ∈ cavityLaws m t) (r : m.Spin → ℝ) (hr : r ∈ stdSimplex ℝ m.Spin)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hmean : ∀ i, m.pi t' i = (1-c)*r i+c*m.pi t i) :
    ∃ ν' ∈ cavityLaws m t', (ν' : Measure (m.Spin → ℝ)) =
      Measure.map (fun μ : m.Spin → ℝ => fun i => (1-c)*r i+c*μ i)
        (ν : Measure (m.Spin → ℝ)) := by
  refine ⟨ν.map (affineMessage_cont m r c).measurable.aemeasurable,
    cavity_affine m t t' ν hν r hr c hc0 hc1 hmean, ?_⟩
  rfl

