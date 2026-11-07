-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.secondQubitDiscard_mapDensity_xor_zzEvenBranchDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:18:55.420187+00:00
-- url     : https://prove2.me/submissions/dfc74c7f-fa60-4c16-be36-ef07b60794e5

import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityBranches
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Discard
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_involutive
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_symm_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_tensor_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenBranchDensity_toOperator
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_branchState
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddBranchDensity_toOperator
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_branchState
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply_basis
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_involutive
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_symm_apply
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_tensor_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenBranchDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzEvenProjector_branchState
attribute [local simp] QEC.Distillation.TwoQubit.zzOddBranchDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.zzOddProjector_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.zzOddProjector_branchState
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply_basis
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
noncomputable section
namespace QEC
namespace Distillation
namespace TwoQubit
open Semantics Semantics.Qubit
open scoped InnerProductSpace TensorProduct
private theorem densityOperator_ext_toOperator
    {rho sigma : DensityOperator QubitSpace}
    (h : rho.toOperator = sigma.toOperator) :
    rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl
private theorem pureOfNonzero_toOperator_of_norm_one
    (state : QubitSpace) (hstate : state ≠ 0)
    (hnorm : ‖state‖ = 1) :
    (DensityOperator.pureOfNonzero state hstate).toOperator =
      (InnerProductSpace.rankOne Complex state state).toLinearMap := by
  rw [DensityOperator.pureOfNonzero_toOperator]
  rw [inner_self_eq_norm_sq_to_K, hnorm]
  norm_num
private theorem zzEvenBranchFirstDensity_toOperator
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    (zzEvenBranchFirstDensity psi h).toOperator =
      (InnerProductSpace.rankOne Complex
        (zzEvenBranchFirstQubit psi h)
        (zzEvenBranchFirstQubit psi h)).toLinearMap := by
  rw [zzEvenBranchFirstDensity]
  exact pureOfNonzero_toOperator_of_norm_one
    (zzEvenBranchFirstQubit psi h)
    (qubitState_ne_zero_of_norm_one
      (zzEvenBranchFirstQubit psi h)
      (zzEvenBranchFirstQubit_norm psi h))
    (zzEvenBranchFirstQubit_norm psi h)
private theorem secondQubitDiscard_rankOne_xor_of_factorized
    (branchState : TwoQubitSpace) (firstQubit : QubitSpace)
    (target : Fin 2)
    (hfactorized :
      tensorRegisterTransport.symm (xorTransport branchState) =
        firstQubit ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex target) :
    (QuantumChannel.comp secondQubitDiscard
      (QuantumChannel.unitaryConj xorTransport))
        (InnerProductSpace.rankOne Complex
          branchState branchState).toLinearMap =
      (InnerProductSpace.rankOne Complex
        firstQubit firstQubit).toLinearMap := by
  rw [QuantumChannel.comp_apply, QuantumChannel.unitaryConj_apply]
  rw [QuditSubsystem.conjOperator_rankOne]
  rw [secondQubitDiscard_apply]
  rw [QuditSubsystem.conjOperator_rankOne]
  rw [hfactorized]
  rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  simp
end TwoQubit
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit
open scoped InnerProductSpace TensorProduct
namespace QEC.Distillation.TwoQubit
theorem _root_.solution
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    (QuantumChannel.comp secondQubitDiscard
      (QuantumChannel.unitaryConj xorTransport)).mapDensity
        (zzEvenBranchDensity psi h) =
      zzEvenBranchFirstDensity psi h := by
  apply densityOperator_ext_toOperator
  rw [QuantumChannel.mapDensity_toOperator]
  rw [zzEvenBranchDensity_toOperator]
  rw [secondQubitDiscard_rankOne_xor_of_factorized
    (zzEvenBranchState psi h)
    (zzEvenBranchFirstQubit psi h)
    0
    (xorTransport_zzEvenBranchState_factorized psi h)]
  exact (zzEvenBranchFirstDensity_toOperator psi h).symm
end QEC.Distillation.TwoQubit
