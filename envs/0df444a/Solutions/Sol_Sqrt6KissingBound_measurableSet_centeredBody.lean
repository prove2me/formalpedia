-- Prove2me | solution 1 for Sqrt6KissingBound.measurableSet_centeredBody
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:13:20.089872+00:00
-- url     : https://prove2.me/submissions/58e4fc35-a01a-413a-b7b1-d1f3f033b82e

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
    MeasurableSet (centeredBody k S x) :=
  hS.preimage (axisTo k x).symm.continuous.measurable
end Sqrt6KissingBound
