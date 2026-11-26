-- Prove2me | solution 1 for Sqrt6KissingBound.lowerBicone_one_disjoint_upperBody3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:21:27.804578+00:00
-- url     : https://prove2.me/submissions/23175933-d922-4453-a60f-0aa361727619

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionThree

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution : Disjoint (lowerBicone 1) upperBody3 := by
  rw [Set.disjoint_left]
  intro y hyl hyu
  have hl : ((standardCoordinates 2).symm y).1 ∈ Set.Ioo 0 a_d3 := hyl.1
  have hu : ((standardCoordinates 2).symm y).1 ∈ Set.Ioo a_d3 1 := hyu.1
  exact lt_asymm hl.2 hu.1
end Sqrt6KissingBound
