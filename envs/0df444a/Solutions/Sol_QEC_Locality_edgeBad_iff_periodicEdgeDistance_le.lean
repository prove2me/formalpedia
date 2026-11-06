-- Prove2me | solution 1 for QEC.Locality.edgeBad_iff_periodicEdgeDistance_le
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T17:49:01.652377+00:00
-- url     : https://prove2.me/submissions/8b2e0b35-41e6-4507-b2af-273480efda4f

import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality

theorem solution
    (w r : ℝ) (t : GridTranslation w) (p : ℝ × ℝ) :
    edgeBad w r t p ↔ periodicEdgeDistance w t p ≤ r := by
  simp [edgeBad, periodicEdgeDistance]
