-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.trace_comp_eq_scalar_of_scalarCompression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:16:46.188659+00:00
-- url     : https://prove2.me/submissions/441d67ba-6d35-4628-a982-431d6adb708b

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_comp_projector_eq_self
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_projector_comp_eq_self
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
    {C : QuantumCode (Qudit.QuditRegister q)} {A : Operator (Qudit.QuditRegister q)}
    {alpha : Complex}
    (hCompression : C.projector.comp (A.comp C.projector) = alpha • C.projector)
    (rho : DensityOperator (Qudit.QuditRegister q))
    (hRho : DensityOperator.SupportedOn C rho) :
    LinearMap.trace Complex (Qudit.QuditRegister q) (A.comp rho.toOperator) = alpha := by
  have hProjectorRho := DensityOperator.supportedOn_projector_comp_eq_self C rho hRho
  have hRhoProjector := DensityOperator.supportedOn_comp_projector_eq_self C rho hRho
  have hProjectorRhoApply (x : Qudit.QuditRegister q) :
      C.projector (rho.toOperator x) = rho.toOperator x := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun T : Operator (Qudit.QuditRegister q) => T x) hProjectorRho
  calc
    LinearMap.trace Complex (Qudit.QuditRegister q) (A.comp rho.toOperator) =
        LinearMap.trace Complex (Qudit.QuditRegister q) (rho.toOperator.comp A) := by
          exact LinearMap.trace_comp_comm' rho.toOperator A
    _ = LinearMap.trace Complex (Qudit.QuditRegister q)
          ((rho.toOperator.comp C.projector).comp A) := by rw [hRhoProjector]
    _ = LinearMap.trace Complex (Qudit.QuditRegister q)
          (C.projector.comp (A.comp rho.toOperator)) := by
            simpa [LinearMap.comp_assoc] using
              (LinearMap.trace_comp_cycle
                (R := Complex) (M := Qudit.QuditRegister q)
                (N := Qudit.QuditRegister q) (P := Qudit.QuditRegister q)
                (f := C.projector) (g := rho.toOperator) (h := A))
    _ = LinearMap.trace Complex (Qudit.QuditRegister q)
          ((C.projector.comp (A.comp C.projector)).comp rho.toOperator) := by
            congr 1
            ext x
            simp only [LinearMap.comp_apply]
            rw [hProjectorRhoApply]
    _ = LinearMap.trace Complex (Qudit.QuditRegister q)
          ((alpha • C.projector).comp rho.toOperator) := by rw [hCompression]
    _ = alpha := by
      rw [show (alpha • C.projector).comp rho.toOperator =
          alpha • (C.projector.comp rho.toOperator) by
            ext x
            simp [LinearMap.comp_apply]]
      rw [hProjectorRho, map_smul, rho.trace_one]
      simp
end QEC.Semantics.QuditSubsystem
