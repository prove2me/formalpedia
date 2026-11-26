-- Prove2me | solution 1 for Sqrt6KissingBound.volumeReal_standardBody3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:27:36.263241+00:00
-- url     : https://prove2.me/submissions/663d2971-5095-4564-ae17-aab871f09d99

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
import Theorems.Thm_Sqrt6KissingBound_measurableSet_upperBody3
import Theorems.Thm_Sqrt6KissingBound_upperBody3_subset
import Theorems.Thm_Sqrt6KissingBound_lowerBicone_one_disjoint_upperBody3
import Theorems.Thm_Sqrt6KissingBound_volumeReal_upperBody3
import Theorems.Thm_Sqrt6KissingBound_lowerBicone_subset
import Theorems.Thm_Sqrt6KissingBound_volumeReal_lowerBicone
import Theorems.Thm_Sqrt6KissingBound_volumeReal_union_of_subsets_ball


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).real standardBody3 =
      ((2 - s3_d3) / 3) * unitBallVolumeReal 2 := by
  rw [standardBody3, volumeReal_union_of_subsets_ball
    lowerBicone_one_disjoint_upperBody3 measurableSet_upperBody3
    (fun y hy => (lowerBicone_subset 1 hy).2)
    (fun y hy => (upperBody3_subset hy).2),
    volumeReal_lowerBicone, volumeReal_upperBody3]
  norm_num
  ring
end Sqrt6KissingBound
