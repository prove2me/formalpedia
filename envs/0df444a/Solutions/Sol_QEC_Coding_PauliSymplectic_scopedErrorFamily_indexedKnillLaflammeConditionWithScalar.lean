-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.scopedErrorFamily_indexedKnillLaflammeConditionWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:48:21.928001+00:00
-- url     : https://prove2.me/submissions/af3b130a-e18e-4665-bf0f-632a6cf841c6

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_matrixElement_eq_phase_mul_inner_of_relative_vector_eq_zero
import Theorems.Thm_QEC_Coding_PauliSymplectic_matrixElement_zero_of_scopedByWeight_pair
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ) :
    Semantics.FiniteKrausFamily.IndexedKnillLaflammeConditionWithScalar
      (scopedErrorFamily (ι := ι) t)
      (binaryCSSQuantumCodeOfDualLe xCode zCode hdual)
      (scopedErrorFamilyKLScalar (ι := ι) t) := by
  intro E F ψ hψ φ hφ
  dsimp [scopedErrorFamily, scopedErrorFamilyKLScalar]
  by_cases hzero :
      (binaryMul (binaryDagger E.1) F.1).vector.xPart = 0 ∧
      (binaryMul (binaryDagger E.1) F.1).vector.zPart = 0
  · have hphase := matrixElement_eq_phase_mul_inner_of_relative_vector_eq_zero
      (E := E.1) (F := F.1) hzero.1 hzero.2 (ψ := ψ) (φ := φ)
    simpa [hzero] using hphase
  · have hnontrivial :
      (binaryMul (binaryDagger E.1) F.1).vector.xPart ≠ 0 ∨
      (binaryMul (binaryDagger E.1) F.1).vector.zPart ≠ 0 := by
        by_cases hx : (binaryMul (binaryDagger E.1) F.1).vector.xPart = 0
        · right
          intro hz
          exact hzero ⟨hx, hz⟩
        · exact Or.inl hx
    have hzeroME := matrixElement_zero_of_scopedByWeight_pair
      xCode zCode hdual hminX hminZ hbound E.2 F.2 hnontrivial hψ hφ
    simpa [hzero] using hzeroME
end QEC.Coding.PauliSymplectic
