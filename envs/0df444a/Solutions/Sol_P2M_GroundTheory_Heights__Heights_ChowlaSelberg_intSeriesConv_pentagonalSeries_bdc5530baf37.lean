-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_pentagonalSeries_bdc5530baf37
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:47.852825+00:00
-- url     : https://prove2.me/submissions/df469dfe-8084-46ab-8235-7d5da2d98e54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaIntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PDeltaIntSeries
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_abs_coeff_pentagonalSeries_le_742b2301d919

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries Filter Topology Finset
open scoped Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg
theorem _root_.solution {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    IntSeriesConv (pentagonalSeries ℤ) r :=
  (summable_geometric_of_lt_one hr hr1).of_nonneg_of_le (fun n ↦ by positivity)
    fun n ↦ (mul_le_of_le_one_left (pow_nonneg hr _) (abs_coeff_pentagonalSeries_le n))
end GroundTheory.Heights₂.Heights.ChowlaSelberg
