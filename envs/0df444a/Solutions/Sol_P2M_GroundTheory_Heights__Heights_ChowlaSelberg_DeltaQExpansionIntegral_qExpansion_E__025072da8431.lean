-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_E__025072da8431
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:49.710689+00:00
-- url     : https://prove2.me/submissions/48049c0d-31cb-4043-9c99-a0affc323dc0

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
theorem _root_.solution :
    qExpansion 1 E₆ = map (Int.castRingHom ℂ) (1 - (504 : ℤ) • sigmaSeries 5) := by
  ext m
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩, coeff_map]
  have hb : bernoulli 6 = 1 / 42 := by decide +kernel
  rcases eq_or_ne m 0 with rfl | hm
  · simp [sigmaSeries]
  · rw [map_sub, map_zsmul]
    simp [hm, sigmaSeries, hb, coeff_one]
    norm_num
end GroundTheory.Heights₂.Heights.ChowlaSelberg.DeltaQExpansionIntegral
