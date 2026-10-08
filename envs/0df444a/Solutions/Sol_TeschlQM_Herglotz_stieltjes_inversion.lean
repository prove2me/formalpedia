-- Prove2me | solution 1 for TeschlQM.Herglotz.stieltjes_inversion
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T20:37:55.151877+00:00
-- url     : https://prove2.me/submissions/5ef50b69-92c8-48e2-982a-86c72f53cc0d

import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Theorems.Thm_TeschlQM_Herglotz_stieltjes_inversion_formula
import Theorems.Thm_TeschlQM_Herglotz_borelTransform_unique

open MeasureTheory Filter Set TeschlQM.Herglotz
open scoped Topology

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∀ ν : Measure ℝ, IsFiniteMeasure ν →
      (∀ z : ℂ, 0 < z.im → borelTransform ν z = borelTransform μ z) → ν = μ) ∧
    ∀ l₁ l₂ : ℝ, l₁ < l₂ →
      Tendsto (fun ε : ℝ =>
          (1 / Real.pi) * ∫ t in l₁..l₂, (borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im)
        (𝓝[>] (0 : ℝ))
        (𝓝 (((μ (Set.Ioo l₁ l₂)).toReal + (μ (Set.Icc l₁ l₂)).toReal) / 2)) := by
  constructor
  · intro ν hν h
    have : IsFiniteMeasure ν := hν
    exact TeschlQM.Herglotz.borelTransform_unique ν μ h
  · exact TeschlQM.Herglotz.stieltjes_inversion_formula μ
