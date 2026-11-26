-- Prove2me | solution 1 for Sqrt6KissingBound.measurableSet_lowerBicone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:07:25.166824+00:00
-- url     : https://prove2.me/submissions/b33d2dc7-cf97-4906-a1c1-31bdeda72534

import Definitions.Def_Sqrt6KissingBound_BodyVolumeAdditivity
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
import Definitions.Def_Sqrt6KissingBound_LinearProfileIntegral
import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Theorems.Thm_Sqrt6KissingBound_measurableSet_rotationalProfile


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped Interval Real
namespace Sqrt6KissingBound
theorem _root_.solution (k : ℕ) : MeasurableSet (lowerBicone k) := by
  exact measurableSet_rotationalProfile (k + 1) measurableSet_Ioo
    (continuous_id.div_const _).measurable
end Sqrt6KissingBound
