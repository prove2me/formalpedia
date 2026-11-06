-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.ScalarCompression.of_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:16:39.951732+00:00
-- url     : https://prove2.me/submissions/8baf246c-11d1-4e6d-8b2d-5315a1c55184

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
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
namespace ScalarCompression
theorem _root_.solution
    {C : QuantumCode (Qudit.QuditRegister q)}
    {A : Operator (Qudit.QuditRegister q)} {a : Complex}
    (ha : a ≠ 0) (hA : ScalarCompression C (a • A)) : ScalarCompression C A := by
  rcases hA with ⟨alpha, hAlpha⟩
  refine ⟨a⁻¹ * alpha, ?_⟩
  calc
    C.projector.comp (A.comp C.projector) =
        (a⁻¹ * a) • (C.projector.comp (A.comp C.projector)) := by
          rw [inv_mul_cancel₀ ha]
          simp
    _ = a⁻¹ • (C.projector.comp ((a • A).comp C.projector)) := by
          ext x
          simp [LinearMap.comp_apply, smul_smul, mul_assoc]
    _ = a⁻¹ • (alpha • C.projector) := by rw [hAlpha]
    _ = (a⁻¹ * alpha) • C.projector := by module
end ScalarCompression
end QEC.Semantics.QuditSubsystem
