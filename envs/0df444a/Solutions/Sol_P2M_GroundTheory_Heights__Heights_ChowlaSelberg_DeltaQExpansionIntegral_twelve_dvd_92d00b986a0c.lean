-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_twelve_dvd_92d00b986a0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:00.615126+00:00
-- url     : https://prove2.me/submissions/bf8d3f63-a1cd-4fb9-9283-a9d40ca6593e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaQExpansionIntegral

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
open UpperHalfPlane ModularForm EisensteinSeries PowerSeries ArithmeticFunction
open scoped MatrixGroups ArithmeticFunction.sigma
noncomputable section
open GroundTheory.Heights₂.Heights.ChowlaSelberg.DeltaQExpansionIntegral
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg.DeltaQExpansionIntegral
theorem _root_.solution (n : ℕ) : 12 ∣ 5 * σ 3 n + 7 * σ 5 n := by
  rw [sigma_apply, sigma_apply, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.dvd_sum fun d _ ↦ ?_
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  generalize (d : ZMod 12) = x
  revert x
  decide
end GroundTheory.Heights₂.Heights.ChowlaSelberg.DeltaQExpansionIntegral
