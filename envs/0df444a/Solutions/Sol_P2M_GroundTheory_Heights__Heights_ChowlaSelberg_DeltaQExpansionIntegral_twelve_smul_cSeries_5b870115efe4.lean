-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_twelve_smul_cSeries_5b870115efe4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:05:07.344952+00:00
-- url     : https://prove2.me/submissions/2bf601c1-81fd-413a-8660-54e79c433c52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaQExpansionIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_twelve_dvd_92d00b986a0c

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
    (12 : ℤ) • cSeries = (5 : ℤ) • sigmaSeries 3 + (7 : ℤ) • sigmaSeries 5 := by
  ext n
  have h := Nat.mul_div_cancel' (twelve_dvd n)
  rw [map_add, map_zsmul, map_zsmul, map_zsmul]
  simp only [cSeries, sigmaSeries, coeff_mk, smul_eq_mul]
  exact_mod_cast h
end GroundTheory.Heights₂.Heights.ChowlaSelberg.DeltaQExpansionIntegral
