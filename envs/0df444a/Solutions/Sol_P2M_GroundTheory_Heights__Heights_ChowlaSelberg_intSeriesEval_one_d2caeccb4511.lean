-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesEval_one_d2caeccb4511
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:42.01322+00:00
-- url     : https://prove2.me/submissions/81df5654-2aa9-4fe8-9cfb-0818f47afa21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaIntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PDeltaIntSeries

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
theorem _root_.solution (z : ℂ) : intSeriesEval 1 z = 1 := by
  rw [intSeriesEval, tsum_eq_single 0 fun n hn ↦ by simp [coeff_one, hn]]
  simp
end GroundTheory.Heights₂.Heights.ChowlaSelberg
