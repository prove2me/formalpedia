-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:34:31.976658+00:00
-- url     : https://prove2.me/submissions/7691421c-ea2b-4114-abc2-2b320a2ccfda

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
import Theorems.Thm_QEC_Semantics_QuditSubsystem_sum_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_adjoint_comp
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
    (rho : DensityOperator S.selectedSystem) :
    (S.replacementFactorizedKraus rho).Complete := by
  have hBasisIdentity :
      ∑ a : Fin (Module.finrank Complex S.selectedSystem),
        S.extendLocal (InnerProductSpace.rankOne Complex
          ((stdOrthonormalBasis Complex S.selectedSystem) a)
          ((stdOrthonormalBasis Complex S.selectedSystem) a)).toLinearMap = 1 := by
    calc
      ∑ a : Fin (Module.finrank Complex S.selectedSystem),
          S.extendLocal (InnerProductSpace.rankOne Complex
            ((stdOrthonormalBasis Complex S.selectedSystem) a)
            ((stdOrthonormalBasis Complex S.selectedSystem) a)).toLinearMap =
          ∑ a : Fin (Module.finrank Complex S.selectedSystem),
            (S.prepareFactorizedBranch
              ((stdOrthonormalBasis Complex S.selectedSystem) a)).comp
              (LinearMap.adjoint (S.prepareFactorizedBranch
                ((stdOrthonormalBasis Complex S.selectedSystem) a))) := by
                  apply Finset.sum_congr rfl
                  intro a _
                  symm
                  exact S.prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
                    ((stdOrthonormalBasis Complex S.selectedSystem) a)
                    ((stdOrthonormalBasis Complex S.selectedSystem) a)
      _ = 1 := S.sum_prepareFactorizedBranch_comp_adjoint_prepareFactorizedBranch
        (stdOrthonormalBasis Complex S.selectedSystem)
  rw [FiniteKrausFamily.Complete, Fintype.sum_prod_type]
  calc
    ∑ i : Fin (S.densityEnsembleSize rho),
        ∑ a : Fin (Module.finrank Complex S.selectedSystem),
          (LinearMap.adjoint ((S.replacementFactorizedKraus rho).operator (i, a))).comp
            ((S.replacementFactorizedKraus rho).operator (i, a)) =
        ∑ i : Fin (S.densityEnsembleSize rho),
          ∑ a : Fin (Module.finrank Complex S.selectedSystem),
            (inner Complex (S.densityEnsembleVectors rho i)
              (S.densityEnsembleVectors rho i)) •
              S.extendLocal (InnerProductSpace.rankOne Complex
                ((stdOrthonormalBasis Complex S.selectedSystem) a)
                ((stdOrthonormalBasis Complex S.selectedSystem) a)).toLinearMap := by
                  apply Finset.sum_congr rfl
                  intro i _
                  apply Finset.sum_congr rfl
                  intro a _
                  exact S.replacementFactorizedKraus_adjoint_comp rho (i, a) (i, a)
    _ = ∑ i : Fin (S.densityEnsembleSize rho),
          (inner Complex (S.densityEnsembleVectors rho i)
            (S.densityEnsembleVectors rho i)) •
            (∑ a : Fin (Module.finrank Complex S.selectedSystem),
              S.extendLocal (InnerProductSpace.rankOne Complex
                ((stdOrthonormalBasis Complex S.selectedSystem) a)
                ((stdOrthonormalBasis Complex S.selectedSystem) a)).toLinearMap) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.smul_sum]
    _ = ∑ i : Fin (S.densityEnsembleSize rho),
          (inner Complex (S.densityEnsembleVectors rho i)
            (S.densityEnsembleVectors rho i)) • (1 : Operator S.factorizedSystem) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [hBasisIdentity]
    _ = 1 := by
      apply LinearMap.ext
      intro x
      calc
        (∑ i : Fin (S.densityEnsembleSize rho),
            (inner Complex (S.densityEnsembleVectors rho i)
              (S.densityEnsembleVectors rho i)) • (1 : Operator S.factorizedSystem)) x =
            (∑ i : Fin (S.densityEnsembleSize rho),
              inner Complex (S.densityEnsembleVectors rho i)
                (S.densityEnsembleVectors rho i)) • x := by
                  simp [Finset.sum_smul]
        _ = x := by rw [S.densityEnsemble_trace_one rho]; simp
end QEC.Semantics.QuditSubsystem
