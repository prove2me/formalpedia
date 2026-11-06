-- Prove2me | solution 1 for QEC.Semantics.validEffect_half_rankOne_of_inner_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:52:18.917783+00:00
-- url     : https://prove2.me/submissions/fe48473d-def8-4bcb-9794-e0dbfc636bc1

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
set_option maxHeartbeats 800000
namespace QEC.Semantics
theorem _root_.solution {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {x : H} (hxx : inner Complex x x = 2) :
    ValidEffect ((2 : Complex)⁻¹ •
      (InnerProductSpace.rankOne Complex x x).toLinearMap) := by
  have hxnorm : (‖x‖ ^ 2 : Complex) = 2 := by
    calc
      (‖x‖ ^ 2 : Complex) = inner Complex x x := (inner_self_eq_norm_sq_to_K x).symm
      _ = 2 := hxx
  let P : Operator H := (2 : Complex)⁻¹ •
    (InnerProductSpace.rankOne Complex x x).toLinearMap
  have hP : P.IsSymmetricProjection := by
    constructor
    · ext x
      simp [P, InnerProductSpace.rankOne_apply]
      rw [hxnorm]
      module
    · have hreal : starRingEnd Complex ((2 : Complex)⁻¹) = (2 : Complex)⁻¹ := by
        rw [map_inv₀]
        have htwo : starRingEnd Complex (2 : Complex) = 2 :=
          map_natCast (starRingEnd Complex) 2
        rw [htwo]
      simpa [P] using
        (InnerProductSpace.isSymmetric_rankOne_self (𝕜 := Complex) x).smul hreal
  have hOne : (1 : Operator H).IsSymmetricProjection := by
    constructor
    · exact one_mul _
    · intro y z
      simp
  refine ⟨hP.isPositive, ?_⟩
  exact (hP.sub_of_range_le_range hOne (by
    intro y _
    exact ⟨y, by simp⟩)).isPositive
end QEC.Semantics
