-- Prove2me | solution 1 for Sqrt6KissingBound.card_mul_volumeReal_le_unitBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:19:55.821926+00:00
-- url     : https://prove2.me/submissions/bf7b6e6a-6cf1-42a5-b996-b5411dace028

import Definitions.Def_Sqrt6KissingBound_Geometry
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Theorems.Thm_Sqrt6KissingBound_sum_volumeReal_le_unitBall

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
namespace Sqrt6KissingBound
theorem _root_.solution (X : Finset ι) (body : ι → Set E)
    (hmeas : ∀ i ∈ X, MeasurableSet (body i))
    (hsub : ∀ i ∈ X, body i ⊆ ball 0 1)
    (hdisj : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → Disjoint (body i) (body j))
    {q : ℝ} (hvol : ∀ i ∈ X, (volume : Measure E).real (body i) = q) :
    (X.card : ℝ) * q ≤ (volume : Measure E).real (ball 0 1) := by
  have h := sum_volumeReal_le_unitBall X body hmeas hsub hdisj
  calc
    (X.card : ℝ) * q = ∑ i ∈ X, q := by simp
    _ = ∑ i ∈ X, (volume : Measure E).real (body i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hvol i hi).symm
    _ ≤ (volume : Measure E).real (ball 0 1) := h
end Sqrt6KissingBound
