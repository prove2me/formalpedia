-- Prove2me | solution 1 for Sqrt6KissingBound.measurableSet_standardBicone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:14:13.118293+00:00
-- url     : https://prove2.me/submissions/915e5bc3-483a-434f-ba05-cf4313cf82db

import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Theorems.Thm_Sqrt6KissingBound_measurableSet_lowerBicone
import Theorems.Thm_Sqrt6KissingBound_measurableSet_upperBicone


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (k : ℕ) : MeasurableSet (standardBicone k) :=
  (measurableSet_lowerBicone k).union (measurableSet_upperBicone k)
end Sqrt6KissingBound
