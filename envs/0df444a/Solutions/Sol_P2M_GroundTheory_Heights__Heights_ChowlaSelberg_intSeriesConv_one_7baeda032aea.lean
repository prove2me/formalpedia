-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_intSeriesConv_one_7baeda032aea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:40.49674+00:00
-- url     : https://prove2.me/submissions/4f7e0e37-6291-4434-939b-cf71c5fb21a4

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
theorem _root_.solution {r : ℝ} : IntSeriesConv 1 r := by
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  simp [coeff_one, show n ≠ 0 by simpa using hn]
end GroundTheory.Heights₂.Heights.ChowlaSelberg
