-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_inducedMap_eq_replacement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:18:34.061224+00:00
-- url     : https://prove2.me/submissions/7c181f62-7941-4b6a-89da-d14e623e50f2

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_inducedMap_rankOne_tmul_eq_replacement
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_linearMap_ext_of_rankOne_basis
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
    (S.replacementFactorizedKraus rho).inducedMap =
      (QuantumChannel.comp (S.prepareFactorized rho) S.erasureChannel).toLinearMap := by
  apply linearMap_ext_of_rankOne_basis
    ((stdOrthonormalBasis Complex S.selectedSystem).tensorProduct
      (stdOrthonormalBasis Complex S.complementSystem))
    (S.replacementFactorizedKraus rho).inducedMap
    (QuantumChannel.comp (S.prepareFactorized rho) S.erasureChannel).toLinearMap
  intro x y
  rcases x with ⟨a, k⟩
  rcases y with ⟨b, l⟩
  simp only [OrthonormalBasis.tensorProduct_apply', QuantumChannel.comp_apply]
  exact S.replacementFactorizedKraus_inducedMap_rankOne_tmul_eq_replacement rho a b
    ((stdOrthonormalBasis Complex S.complementSystem) k)
    ((stdOrthonormalBasis Complex S.complementSystem) l)
end QEC.Semantics.QuditSubsystem
