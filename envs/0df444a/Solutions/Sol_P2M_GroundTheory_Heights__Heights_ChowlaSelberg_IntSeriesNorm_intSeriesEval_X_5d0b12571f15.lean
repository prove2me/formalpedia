-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_intSeriesEval_X_5d0b12571f15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:23.298718+00:00
-- url     : https://prove2.me/submissions/8cd14535-f0f1-4ad6-825f-1861512d0ab8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesNorm

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
open PowerSeries
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
theorem _root_.solution (z : ℂ) : intSeriesEval X z = z := by
  rw [intSeriesEval, tsum_eq_single 1]
  · simp
  · intro n hn; simp [coeff_X, hn]
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
