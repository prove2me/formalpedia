-- Prove2me | solution 1 for Sqrt6KissingBound.volumeReal_centeredBody
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:13:21.141064+00:00
-- url     : https://prove2.me/submissions/c3893e27-c80a-4aec-93e2-4a1b2295cb98

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_CenteredBody

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (k + 2)))} (hS : MeasurableSet S)
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    (volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).real
        (centeredBody k S x) =
      (volume : Measure (EuclideanSpace ℝ (Fin (k + 2)))).real S := by
  rw [centeredBody, Measure.real,
    (axisTo k x).symm.measurePreserving.measure_preimage hS.nullMeasurableSet]
  rfl
end Sqrt6KissingBound
