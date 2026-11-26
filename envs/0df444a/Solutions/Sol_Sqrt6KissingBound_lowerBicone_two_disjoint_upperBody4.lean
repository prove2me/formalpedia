-- Prove2me | solution 1 for Sqrt6KissingBound.lowerBicone_two_disjoint_upperBody4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:22:45.233394+00:00
-- url     : https://prove2.me/submissions/eb8ea667-28af-4a1a-b47a-bc0d84ec21c5

import Definitions.Def_Sqrt6KissingBound_CenteredBody
import Definitions.Def_Sqrt6KissingBound_BallVolumes
import Definitions.Def_Sqrt6KissingBound_DimensionFour

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
set_option maxHeartbeats 800000
namespace Sqrt6KissingBound
theorem _root_.solution : Disjoint (lowerBicone 2) upperBody4 := by
  rw [Set.disjoint_left]
  intro y hyl hyu
  let p := (standardCoordinates 3).symm y
  have hl : p.1 ∈ Set.Ioo 0 a_d4 := hyl.1
  have hu : p.1 ∈ Set.Ioo a_d4 1 := hyu.1
  exact lt_asymm hl.2 hu.1
end Sqrt6KissingBound
