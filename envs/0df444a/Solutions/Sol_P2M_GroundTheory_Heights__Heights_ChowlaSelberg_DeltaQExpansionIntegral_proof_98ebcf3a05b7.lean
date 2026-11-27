-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_proof_98ebcf3a05b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:14.142606+00:00
-- url     : https://prove2.me/submissions/6d9cdfaf-8268-4ed6-a8ab-646039e0af2e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_DeltaQExpansionIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_E__6e5ee9fb4866
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_E__025072da8431
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_twelve_smul_cSeries_5b870115efe4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_discriminant_smul_9d2599ecb76f

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
theorem _root_.solution : Statement := by
  set A := sigmaSeries 3
  set B := sigmaSeries 5
  set Ez : PowerSeries ℤ := 100 * A ^ 2 + 8000 * A ^ 3 - 147 * B ^ 2 + cSeries with hEz
  have hC := twelve_smul_cSeries
  simp only [zsmul_eq_mul, Int.cast_ofNat] at hC
  have hring : (1 + (240 : ℤ) • A) ^ 3 - (1 - (504 : ℤ) • B) ^ 2 = 1728 * Ez := by
    simp only [zsmul_eq_mul, Int.cast_ofNat, hEz]
    linear_combination (-144 : PowerSeries ℤ) * hC
  have key : qExpansion 1 ModularForm.discriminant = map (Int.castRingHom ℂ) Ez := by
    have h2 : (1728 : ℂ) • map (Int.castRingHom ℂ) Ez = qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
      rw [qExpansion_E₄, qExpansion_E₆, ← map_pow, ← map_pow, ← map_sub, hring, map_mul,
        map_ofNat, Algebra.smul_def, map_ofNat]
    exact smul_right_injective _ (by norm_num : (1728 : ℂ) ≠ 0)
      (qExpansion_discriminant_smul.trans h2.symm)
  have h0 : constantCoeff Ez = 0 := by
    simp [hEz, A, B, sigmaSeries, cSeries]
  obtain ⟨D, hD⟩ := X_dvd_iff.mpr h0
  refine ⟨D, ?_, hD ▸ key⟩
  have h1 := discriminant_qExpansion_coeff_one
  rw [key, hD, coeff_map, coeff_succ_X_mul, eq_intCast] at h1
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact_mod_cast h1
end GroundTheory.Heights₂.Heights.ChowlaSelberg.DeltaQExpansionIntegral
