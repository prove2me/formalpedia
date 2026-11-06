-- Prove2me | solution 1 for QEC.Locality.phase_gridOrigin
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T17:49:02.630221+00:00
-- url     : https://prove2.me/submissions/f594a5a4-90d1-4769-8ecf-02738aaba799

import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality

theorem solution (w : ℝ) (t : GridTranslation w) :
    phase w (gridOrigin w t) = t := by
  ext <;> exact Quotient.out_eq _
