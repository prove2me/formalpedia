-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_intSeries_term_cbde42f63863
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:52:06.06677+00:00
-- url     : https://prove2.me/submissions/306d40dc-371c-42e4-b787-3fbbf5d7d2e6

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


theorem solution (F : PowerSeries ℤ) (z : ℂ) (n : ℕ) :
    ‖((coeff n F : ℤ) : ℂ) * z ^ n‖ = |((coeff n F : ℤ) : ℝ)| * ‖z‖ ^ n := by
  simp [norm_mul, norm_pow, Complex.norm_intCast]
