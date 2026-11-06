-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.trace_comp_pureOfNonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:16:50.799713+00:00
-- url     : https://prove2.me/submissions/79b51980-74d2-4294-8a51-a71a90150565

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
theorem _root_.solution
    (A : Operator (Qudit.QuditRegister q)) (x : Qudit.QuditRegister q) (hx : x ≠ 0) :
    LinearMap.trace Complex (Qudit.QuditRegister q)
      (A.comp (DensityOperator.pureOfNonzero x hx).toOperator) =
      (inner Complex x x)⁻¹ * inner Complex x (A x) := by
  rw [DensityOperator.pureOfNonzero_toOperator]
  have hComp : A.comp (InnerProductSpace.rankOne Complex x x).toLinearMap =
      (InnerProductSpace.rankOne Complex (A x) x).toLinearMap := by
    ext y
    simp [LinearMap.comp_apply]
  calc
    LinearMap.trace Complex (Qudit.QuditRegister q)
        (A.comp ((inner Complex x x)⁻¹ •
          (InnerProductSpace.rankOne Complex x x).toLinearMap)) =
        LinearMap.trace Complex (Qudit.QuditRegister q)
          ((inner Complex x x)⁻¹ •
            (A.comp (InnerProductSpace.rankOne Complex x x).toLinearMap)) := by
              congr 1
              ext y
              simp [LinearMap.comp_apply]
    _ = (inner Complex x x)⁻¹ * inner Complex x (A x) := by
      rw [map_smul, hComp, InnerProductSpace.trace_rankOne]
      simp [smul_eq_mul]
end QEC.Semantics.QuditSubsystem
