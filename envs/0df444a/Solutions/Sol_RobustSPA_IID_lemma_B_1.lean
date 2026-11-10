-- Prove2me | solution 1 for RobustSPA.IID.lemma_B_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T17:56:19.819252+00:00
-- url     : https://prove2.me/submissions/e464810a-65a4-4891-91b3-ec94c41c3e4e

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting

open MeasureTheory Set RobustSPA.IID

theorem solution : ¬ (∀ (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) (h h' : ℝ → ℝ)
    (hcont : ContinuousOn h (Set.Icc 0 1))
    (hderiv : ∀ v ∈ Set.Ioo (0 : ℝ) 1, v ≠ r → HasDerivAt h (h' v) v)
    (hint : IntervalIntegrable h' MeasureTheory.volume 0 1)
    (G : ProbabilityMeasure ℝ) (hG : (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0),
    ∫ v in Set.Icc (0 : ℝ) 1, h v ∂(G : Measure ℝ) =
      h 0 * cdfOf G r + ∫ v in (0 : ℝ)..r, h' v * (cdfOf G r - cdfOf G v) +
        h r * (cdfOf G 1 - cdfOf G r) + ∫ v in r..1, h' v * (cdfOf G 1 - cdfOf G v)) := by
  intro H
  let G : ProbabilityMeasure ℝ := ⟨Measure.dirac 1, inferInstance⟩
  have hG : (G : Measure ℝ) (Set.Icc 0 1)ᶜ = 0 := by
    show Measure.dirac (1 : ℝ) (Set.Icc 0 1)ᶜ = 0
    simp [Measure.dirac_apply' _ measurableSet_Icc.compl, Set.indicator]
  have hr : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have heq := H 0 hr (fun _ => 1) (fun _ => 0) continuousOn_const
    (fun v _ _ => hasDerivAt_const v 1) intervalIntegrable_const G hG
  have hLHS : ∫ v in Set.Icc (0 : ℝ) 1, (1 : ℝ) ∂(G : Measure ℝ) = 1 := by
    rw [setIntegral_const, smul_eq_mul, mul_one]
    show (Measure.dirac (1 : ℝ)).real (Set.Icc 0 1) = 1
    simp [Measure.real, Measure.dirac_apply' _ measurableSet_Icc, Set.indicator]
  have hcdf0 : cdfOf (G : Measure ℝ) 0 = 0 := by
    show (Measure.dirac (1 : ℝ) (Set.Iic 0)).toReal = 0
    simp [Measure.dirac_apply' _ measurableSet_Iic, Set.indicator]
    norm_num
  rw [hLHS, hcdf0, intervalIntegral.integral_same] at heq
  norm_num at heq
