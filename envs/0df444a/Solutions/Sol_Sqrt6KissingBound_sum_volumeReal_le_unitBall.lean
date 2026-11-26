-- Prove2me | solution 1 for Sqrt6KissingBound.sum_volumeReal_le_unitBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:18:43.142798+00:00
-- url     : https://prove2.me/submissions/70bd1b58-ad65-4f43-b19b-f9942ffd9873

import Definitions.Def_Sqrt6KissingBound_Geometry
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Sqrt6KissingBound_VolumePacking

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
    (hdisj : ∀ i ∈ X, ∀ j ∈ X, i ≠ j → Disjoint (body i) (body j)) :
    (∑ i ∈ X, (volume : Measure E).real (body i)) ≤
      (volume : Measure E).real (ball 0 1) := by
  let μ : Measure E := (volume : Measure E).restrict (ball 0 1)
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.2
      (measure_ball_lt_top (μ := (volume : Measure E))).ne
  have hpack :
      (∑ i ∈ X, μ.real (body i)) ≤ μ.real Set.univ := by
    apply sum_measureReal_le_measureReal_univ
    · intro i hi
      exact hmeas i hi
    · intro i hi j hj hij
      exact hdisj i hi j hj hij
  have hbody (i : ι) (hi : i ∈ X) :
      μ.real (body i) = (volume : Measure E).real (body i) := by
    simp only [μ, Measure.real, Measure.restrict_apply (hmeas i hi)]
    rw [inter_eq_self_of_subset_left (hsub i hi)]
  have huniv : μ.real Set.univ =
      (volume : Measure E).real (ball 0 1) := by
    simp [μ, Measure.real]
  calc
    (∑ i ∈ X, (volume : Measure E).real (body i)) =
        ∑ i ∈ X, μ.real (body i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (hbody i hi).symm
    _ ≤ μ.real Set.univ := hpack
    _ = (volume : Measure E).real (ball 0 1) := huniv
end Sqrt6KissingBound
