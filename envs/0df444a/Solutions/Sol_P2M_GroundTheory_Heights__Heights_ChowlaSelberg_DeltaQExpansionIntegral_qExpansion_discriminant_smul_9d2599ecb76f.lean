-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_DeltaQExpansionIntegral_qExpansion_discriminant_smul_9d2599ecb76f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:59.883454+00:00
-- url     : https://prove2.me/submissions/0c67417d-babe-4c61-b1ed-356d30fef003

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
    (1728 : ℂ) • qExpansion 1 ModularForm.discriminant =
      qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
  have e : (1728 : ℂ) • (⇑CuspForm.discriminant) = ⇑(E₄.pow 3) - ⇑(E₆.pow 2) := by
    funext τ
    simp only [Pi.smul_apply, Pi.sub_apply, ModularForm.coe_pow, Pi.pow_apply, smul_eq_mul,
      CuspForm.coe_discriminant, discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  rw [← ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ 3,
    ← ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₆ 2,
    ← ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL (E₄.pow 3) (E₆.pow 2), ← e,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (1728 : ℂ) CuspForm.discriminant]
  rfl
end GroundTheory.Heights₂.Heights.ChowlaSelberg.DeltaQExpansionIntegral
