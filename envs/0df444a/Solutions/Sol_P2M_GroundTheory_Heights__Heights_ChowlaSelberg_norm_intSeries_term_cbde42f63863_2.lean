-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_norm_intSeries_term_cbde42f63863
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:59.223801+00:00
-- url     : https://prove2.me/submissions/fc619b97-f371-45aa-87d9-ed157b07dedb

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
theorem _root_.solution (F : PowerSeries ℤ) (z : ℂ) (n : ℕ) :
    ‖((coeff n F : ℤ) : ℂ) * z ^ n‖ = |((coeff n F : ℤ) : ℝ)| * ‖z‖ ^ n := by
  rw [norm_mul, norm_pow, Complex.norm_intCast]
end GroundTheory.Heights₂.Heights.ChowlaSelberg
