-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.replacementKraus_adjoint_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:32:54.196434+00:00
-- url     : https://prove2.me/submissions/4a1662d2-7c49-486f-a332-1e1e89c20186

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_adjoint_comp
import Theorems.Thm_QEC_Semantics_Correctable_unitaryTransport
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_KnillLaflamme_unitaryTransport
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


attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator

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
set_option maxHeartbeats 800000
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem)
    (p r : Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) :
    (LinearMap.adjoint ((S.replacementKraus rho).operator p)).comp
      ((S.replacementKraus rho).operator r) =
      (inner Complex (S.densityEnsembleVectors rho p.1)
        (S.densityEnsembleVectors rho r.1)) •
        S.extendLocalToRegister (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)).toLinearMap := by
  let U := S.registerFactorization.symm
  have hFactor := S.replacementFactorizedKraus_adjoint_comp rho p r
  apply LinearMap.ext
  intro x
  calc
    ((LinearMap.adjoint ((S.replacementKraus rho).operator p)).comp
        ((S.replacementKraus rho).operator r)) x =
        U (((LinearMap.adjoint ((S.replacementFactorizedKraus rho).operator p)).comp
          ((S.replacementFactorizedKraus rho).operator r)) (U.symm x)) := by
            simp [replacementKraus, U, FiniteKrausFamily.unitaryTransport,
              LinearMap.comp_apply,
              S.registerFactorization.adjoint_toLinearMap,
              S.registerFactorization.adjoint_symm_toLinearMap]
    _ = U (((inner Complex (S.densityEnsembleVectors rho p.1)
        (S.densityEnsembleVectors rho r.1)) •
        S.extendLocal (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)).toLinearMap) (U.symm x)) := by
            rw [hFactor]
    _ = ((inner Complex (S.densityEnsembleVectors rho p.1)
        (S.densityEnsembleVectors rho r.1)) •
        S.extendLocalToRegister (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)).toLinearMap) x := by
            simp [U, extendLocalToRegister, UnitaryTransport.conjOperator]
end QEC.Semantics.QuditSubsystem
