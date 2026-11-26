-- Prove2me | solution 1 for Sqrt6KissingBound.volumeReal_centeredBicone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:27:31.02946+00:00
-- url     : https://prove2.me/submissions/02910b00-09d3-404a-bc28-69ae02347cc8

import Definitions.Def_Sqrt6KissingBound_BiconeVolume
import Definitions.Def_Sqrt6KissingBound_VolumePacking
import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Theorems.Thm_Sqrt6KissingBound_measurableSet_standardBicone
import Theorems.Thm_Sqrt6KissingBound_volumeReal_standardBicone


set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (k : ℕ)
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).real
        (centeredBicone k x) =
      (1 / ((k + 2) * 2 ^ (k + 1))) * unitBallVolumeReal (k + 1) := by
  rw [centeredBicone, Measure.real,
    (axisTo k x).symm.measurePreserving.measure_preimage
      (measurableSet_standardBicone k).nullMeasurableSet,
    ← Measure.real]
  exact volumeReal_standardBicone k
end Sqrt6KissingBound
