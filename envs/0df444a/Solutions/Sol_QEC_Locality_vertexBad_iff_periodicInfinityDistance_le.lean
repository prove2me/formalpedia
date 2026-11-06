-- Prove2me | solution 1 for QEC.Locality.vertexBad_iff_periodicInfinityDistance_le
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T17:49:00.567887+00:00
-- url     : https://prove2.me/submissions/4c55fb24-18cc-4931-b3e7-2c2338c2a353

import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling

set_option autoImplicit false
open MeasureTheory Set Metric
noncomputable section
open scoped ENNReal
open QEC QEC.Locality

theorem solution
    (w r : ℝ) (t : GridTranslation w) (p : ℝ × ℝ) :
    vertexBad w r t p ↔ periodicInfinityDistance w t p ≤ r := by
  simp [vertexBad, periodicInfinityDistance]
