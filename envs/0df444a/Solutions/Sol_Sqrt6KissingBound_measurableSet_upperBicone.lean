-- Prove2me | solution 1 for Sqrt6KissingBound.measurableSet_upperBicone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:11:36.903858+00:00
-- url     : https://prove2.me/submissions/cb0d1ee4-baf3-4d21-960e-05f8629d6cf9

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
theorem _root_.solution (k : ℕ) : MeasurableSet (upperBicone k) := by
  exact measurableSet_rotationalProfile (k + 1) measurableSet_Ioo
    (continuous_const.mul (continuous_const.sub continuous_id)).measurable
end Sqrt6KissingBound
