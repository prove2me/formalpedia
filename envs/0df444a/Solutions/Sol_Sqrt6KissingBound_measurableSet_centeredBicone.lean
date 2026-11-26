-- Prove2me | solution 1 for Sqrt6KissingBound.measurableSet_centeredBicone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:20:17.173465+00:00
-- url     : https://prove2.me/submissions/db79242a-0478-4fbb-b32c-4632960dbf95

import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Theorems.Thm_Sqrt6KissingBound_measurableSet_standardBicone

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (k : ℕ)
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    MeasurableSet (centeredBicone k x) :=
  (measurableSet_standardBicone k).preimage (axisTo k x).symm.continuous.measurable
end Sqrt6KissingBound
