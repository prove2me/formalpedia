-- Prove2me | solution 1 for Sqrt6KissingBound.volume_rotationalProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:21:10.320467+00:00
-- url     : https://prove2.me/submissions/5faa3d6e-8354-48a9-a1ae-de73e4dffd3b

import Definitions.Def_Sqrt6KissingBound_CoordinateVolume
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Theorems.Thm_Sqrt6KissingBound_measurableSet_profileRegion
import Theorems.Thm_Sqrt6KissingBound_volume_profileRegion
import Theorems.Thm_Sqrt6KissingBound_standardCoordinates_measurePreserving


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace Sqrt6KissingBound
theorem _root_.solution (d : ℕ) {s : Set ℝ} (hs : MeasurableSet s)
    {g : ℝ → ℝ} (hg : Measurable g) :
    (volume : Measure (EuclideanSpace ℝ (Fin (d + 1))))
        (rotationalProfile d s g) =
      ∫⁻ t in s, (volume : Measure (EuclideanSpace ℝ (Fin d))) (ball 0 (g t)) := by
  calc
    (volume : Measure (EuclideanSpace ℝ (Fin (d + 1))))
          (rotationalProfile d s g) =
        (volume : Measure (ℝ × (Fin d → ℝ))) (profileRegion d s g) := by
          exact (standardCoordinates_measurePreserving d).symm.measure_preimage
            (measurableSet_profileRegion d hs hg).nullMeasurableSet
    _ = _ := volume_profileRegion d hs hg
end Sqrt6KissingBound
