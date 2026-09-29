-- Prove2me | solution 1 for Statistics.prod_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-22T17:34:50.367006+00:00
-- url     : https://prove2.me/submissions/72ec53d0-9c03-4c6a-b6db-b37d0db08108

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space

section



open MeasureTheory Measure
open scoped ENNReal

namespace Statistics

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Tilting the image of a section by a density is the image of the tilt. -/
theorem withDensity_map_prodMk (x : α) (η : Measure β) {g : α × β → ℝ≥0∞} (hg : Measurable g) :
    (η.map (Prod.mk x)).withDensity g
      = (η.withDensity (fun y => g (x, y))).map (Prod.mk x) := by
  ext A hA
  rw [withDensity_apply _ hA, Measure.map_apply measurable_prodMk_left hA,
    withDensity_apply _ (measurable_prodMk_left hA),
    Measure.restrict_map measurable_prodMk_left hA,
    lintegral_map hg measurable_prodMk_left]

/-- A product of tilted measures is the product tilted by the product density. -/
theorem prod_withDensity_aux (η₁ : Measure α) (η₂ : Measure β) [SigmaFinite η₁] [SigmaFinite η₂]
    {f₁ : α → ℝ≥0∞} {f₂ : β → ℝ≥0∞} (h₁ : Measurable f₁) (h₂ : Measurable f₂)
    [SigmaFinite (η₁.withDensity f₁)] [SigmaFinite (η₂.withDensity f₂)] :
    (η₁.prod η₂).withDensity (fun z => f₁ z.1 * f₂ z.2)
      = (η₁.withDensity f₁).prod (η₂.withDensity f₂) := by
  refine (Measure.prod_eq (μ := η₁.withDensity f₁) (ν := η₂.withDensity f₂) fun s t hs ht => ?_).symm
  rw [withDensity_apply _ (hs.prod ht), ← Measure.prod_restrict,
    lintegral_prod_mul h₁.aemeasurable h₂.aemeasurable,
    withDensity_apply _ hs, withDensity_apply _ ht]

end Statistics

end

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

theorem solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (η₁ : Measure α) (η₂ : Measure β) [SigmaFinite η₁] [SigmaFinite η₂]
    {f₁ : α → ℝ≥0∞} {f₂ : β → ℝ≥0∞} (h₁ : Measurable f₁) (h₂ : Measurable f₂)
    [SigmaFinite (η₁.withDensity f₁)] [SigmaFinite (η₂.withDensity f₂)] :
    (η₁.prod η₂).withDensity (fun z => f₁ z.1 * f₂ z.2)
      = (η₁.withDensity f₁).prod (η₂.withDensity f₂) :=
  Statistics.prod_withDensity_aux η₁ η₂ h₁ h₂
