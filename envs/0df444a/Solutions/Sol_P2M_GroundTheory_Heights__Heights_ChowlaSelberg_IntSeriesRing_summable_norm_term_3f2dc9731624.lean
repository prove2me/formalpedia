-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesRing_summable_norm_term_3f2dc9731624
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:58.869812+00:00
-- url     : https://prove2.me/submissions/54647ca7-b5eb-4360-9309-bd4c531793e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesRing

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
open PowerSeries Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
theorem _root_.solution {F : PowerSeries ℤ} {r : ℝ} (hF : IntSeriesConv F r) {z : ℂ}
    (hz : ‖z‖ ≤ r) : Summable fun n ↦ ‖((coeff n F : ℤ) : ℂ) * z ^ n‖ :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ by
    rw [norm_mul, norm_pow, Complex.norm_intCast]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz n) (abs_nonneg _)) hF
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesRing
