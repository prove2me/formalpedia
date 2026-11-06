-- Prove2me | solution 2 for QEC.Locality.phase_gridOrigin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:16:42.200149+00:00
-- url     : https://prove2.me/submissions/490b94ab-ebbf-4e53-a364-00b1ea935e0d

import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality
attribute [local instance] QEC.Locality.instClassicalDecidable
namespace QEC.Locality
theorem _root_.solution (w : ℝ) (t : GridTranslation w) :
    phase w (gridOrigin w t) = t := by
  ext <;> exact Quotient.out_eq _
end QEC.Locality
