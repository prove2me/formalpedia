-- Prove2me | solution 1 for Sqrt6KissingBound.volumeReal_union_of_subsets_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:04:20.622599+00:00
-- url     : https://prove2.me/submissions/a384b340-81a7-43e0-b728-9da2e8d066ec

import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Definitions.Def_Sqrt6KissingBound_BodyVolumeAdditivity

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution {n : ℕ}
    {S T : Set (EuclideanSpace ℝ (Fin n))}
    (hd : Disjoint S T) (hT : MeasurableSet T)
    (hSball : S ⊆ ball 0 1) (hTball : T ⊆ ball 0 1) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).real (S ∪ T) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real S +
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real T := by
  exact measureReal_union hd hT
    (lt_of_le_of_lt (measure_mono hSball) measure_ball_lt_top).ne
    (lt_of_le_of_lt (measure_mono hTball) measure_ball_lt_top).ne
end Sqrt6KissingBound
