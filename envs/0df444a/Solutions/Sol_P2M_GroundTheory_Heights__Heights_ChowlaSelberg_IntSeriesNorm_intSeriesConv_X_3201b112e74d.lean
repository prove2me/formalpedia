-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_intSeriesConv_X_3201b112e74d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:58.257823+00:00
-- url     : https://prove2.me/submissions/f735bc03-0f99-4181-9934-f094036d102e

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
theorem _root_.solution (r : ℝ) : IntSeriesConv X r := by
  apply summable_of_ne_finset_zero (s := {1})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [coeff_X, hn]
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
