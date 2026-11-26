-- Prove2me | solution 1 for Sqrt6KissingBound.volumeReal_standardBody4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:26:41.751666+00:00
-- url     : https://prove2.me/submissions/c9bcd611-22c7-4036-a9a9-f461eb151dbf

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Theorems.Thm_Sqrt6KissingBound_measurableSet_upperBody4
import Theorems.Thm_Sqrt6KissingBound_upperBody4_subset
import Theorems.Thm_Sqrt6KissingBound_lowerBicone_two_disjoint_upperBody4
import Theorems.Thm_Sqrt6KissingBound_volumeReal_upperBody4
import Theorems.Thm_Sqrt6KissingBound_lowerBicone_subset
import Theorems.Thm_Sqrt6KissingBound_volumeReal_lowerBicone
import Theorems.Thm_Sqrt6KissingBound_volumeReal_union_of_subsets_ball


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution :
    (volume : Measure (EuclideanSpace ℝ (Fin 4))).real standardBody4 =
      ((265352 - 153195 * s3_d4) / 320) * unitBallVolumeReal 3 := by
  rw [standardBody4, volumeReal_union_of_subsets_ball
    lowerBicone_two_disjoint_upperBody4 measurableSet_upperBody4
    (fun y hy => (lowerBicone_subset 2 hy).2)
    (fun y hy => (upperBody4_subset hy).2),
    volumeReal_lowerBicone, volumeReal_upperBody4]
  ring
end Sqrt6KissingBound
