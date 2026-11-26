-- Prove2me | solution 1 for Sqrt6KissingBound.standardBody4_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:25:05.887386+00:00
-- url     : https://prove2.me/submissions/e44c479d-a866-4aa1-bca6-c0042394ce9b

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour
import Theorems.Thm_Sqrt6KissingBound_upperBody4_subset
import Theorems.Thm_Sqrt6KissingBound_lowerBicone_subset


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution : standardBody4 ⊆ strictCone (standardAxis 3) ∩ ball 0 1 :=
  union_subset (lowerBicone_subset 2) upperBody4_subset
end Sqrt6KissingBound
