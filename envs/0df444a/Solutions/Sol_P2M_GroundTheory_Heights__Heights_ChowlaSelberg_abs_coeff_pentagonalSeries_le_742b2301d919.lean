-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_abs_coeff_pentagonalSeries_le_742b2301d919
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:42.707747+00:00
-- url     : https://prove2.me/submissions/4595e64a-dc04-4f2c-8132-827b20530012

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
theorem _root_.solution (n : ℕ) :
    |((coeff n (pentagonalSeries ℤ) : ℤ) : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs, ← Int.cast_one (R := ℝ), Int.cast_le]
  simp only [pentagonalSeries, coeff_mk]
  split_ifs with h
  · rcases Int.units_eq_one_or (Int.negOnePow h.choose) with h' | h' <;> simp [h']
  · simp
end GroundTheory.Heights₂.Heights.ChowlaSelberg
