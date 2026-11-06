-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_adjoint_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:31:00.734492+00:00
-- url     : https://prove2.me/submissions/483a50cf-7469-416b-86ea-7ac3577caad1

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
import Theorems.Thm_QEC_Semantics_QuditSubsystem_adjoint_prepareFactorizedBranch_comp_cross
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
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
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem)
    (p r : Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) :
    (LinearMap.adjoint ((S.replacementFactorizedKraus rho).operator p)).comp
      ((S.replacementFactorizedKraus rho).operator r) =
      (inner Complex (S.densityEnsembleVectors rho p.1)
        (S.densityEnsembleVectors rho r.1)) •
        S.extendLocal (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)).toLinearMap := by
  rw [S.replacementFactorizedKraus_operator, S.replacementFactorizedKraus_operator]
  rw [LinearMap.adjoint_comp]
  simp only [LinearMap.adjoint_adjoint]
  calc
    ((S.prepareFactorizedBranch
        ((stdOrthonormalBasis Complex S.selectedSystem) p.2)).comp
        (LinearMap.adjoint (S.prepareFactorizedBranch (S.densityEnsembleVectors rho p.1)))).comp
      ((S.prepareFactorizedBranch (S.densityEnsembleVectors rho r.1)).comp
        (LinearMap.adjoint (S.prepareFactorizedBranch
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)))) =
        (S.prepareFactorizedBranch
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)).comp
          (((LinearMap.adjoint (S.prepareFactorizedBranch
            (S.densityEnsembleVectors rho p.1))).comp
            (S.prepareFactorizedBranch (S.densityEnsembleVectors rho r.1))).comp
            (LinearMap.adjoint (S.prepareFactorizedBranch
              ((stdOrthonormalBasis Complex S.selectedSystem) r.2)))) := by
                rfl
    _ = (S.prepareFactorizedBranch
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)).comp
          (((inner Complex (S.densityEnsembleVectors rho p.1)
            (S.densityEnsembleVectors rho r.1)) • (1 : Operator S.complementSystem)).comp
            (LinearMap.adjoint (S.prepareFactorizedBranch
              ((stdOrthonormalBasis Complex S.selectedSystem) r.2)))) := by
                rw [S.adjoint_prepareFactorizedBranch_comp_cross]
    _ = (inner Complex (S.densityEnsembleVectors rho p.1)
          (S.densityEnsembleVectors rho r.1)) •
        ((S.prepareFactorizedBranch
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)).comp
          (LinearMap.adjoint (S.prepareFactorizedBranch
            ((stdOrthonormalBasis Complex S.selectedSystem) r.2)))) := by
              ext x
              simp [LinearMap.comp_apply]
    _ = (inner Complex (S.densityEnsembleVectors rho p.1)
          (S.densityEnsembleVectors rho r.1)) •
        S.extendLocal (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2)
          ((stdOrthonormalBasis Complex S.selectedSystem) r.2)).toLinearMap := by
              rw [S.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch]
end QEC.Semantics.QuditSubsystem
