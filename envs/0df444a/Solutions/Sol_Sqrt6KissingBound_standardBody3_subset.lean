-- Prove2me | solution 1 for Sqrt6KissingBound.standardBody3_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:22:29.415301+00:00
-- url     : https://prove2.me/submissions/773d0186-5680-44f5-9926-2d52e7a87af9

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree
import Theorems.Thm_Sqrt6KissingBound_upperBody3_subset
import Theorems.Thm_Sqrt6KissingBound_lowerBicone_subset


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution : standardBody3 ⊆ strictCone (standardAxis 2) ∩ ball 0 1 :=
  union_subset (lowerBicone_subset 1) upperBody3_subset
end Sqrt6KissingBound
