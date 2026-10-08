-- Prove2me | solution 1 for RadGauss.Structural.theorem_12_part_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:45:17.82799+00:00
-- url     : https://prove2.me/submissions/03f6f686-cd00-4643-964f-8eb92c56faf9

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Pointwise

open MeasureTheory RadGauss.RiskBound in
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F H : Set (X → ℝ)) (hFH : F ⊆ H) :
    RadGauss.RiskBound.rademacherComplexity μ n F ≤ RadGauss.RiskBound.rademacherComplexity μ n H := by
  unfold rademacherComplexity
  refine lintegral_mono fun x => ?_
  unfold empiricalRademacher
  exact mul_le_mul_right (Finset.sum_le_sum fun σ _ =>
    biSup_mono fun (g : X → ℝ) (hg : g ∈ F) => hFH hg) _
