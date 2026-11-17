-- Prove2me | solution 1 for completion_apply_union_isNullSet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:52:01.169218+00:00
-- url     : https://prove2.me/submissions/cdd31857-f31e-4f8e-9d2e-f73a364b55a0

import Theorems.Thm_measure_eq_zero_of_isNullSet
import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_6_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_9_F000
import Mathlib.MeasureTheory.Measure.NullMeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open Set

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A N : Set Ω} (_hA : MeasurableSet A) (hN : IsNullSet μ N) :
    completionMeasure μ (A ∪ N) = μ A := by
  have hN0 : μ N = 0 := measure_eq_zero_of_isNullSet hN
  change μ (A ∪ N) = μ A
  apply le_antisymm
  · calc
      μ (A ∪ N) ≤ μ A + μ N := measure_union_le A N
      _ = μ A := by rw [hN0, add_zero]
  · exact measure_mono (subset_union_left : A ⊆ A ∪ N)
