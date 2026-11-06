-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.syndromeSeparatedByCheckSet_of_scopedByWeight_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:29:27.972655+00:00
-- url     : https://prove2.me/submissions/6086ef72-c2f4-4524-942a-73fc8c22b4c8

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_weight_binaryMul_le
import Theorems.Thm_QEC_Coding_PauliSymplectic_checkDistinguishes_binary_of_weight_lt_dualMinimumDistances
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
    (xCode zCode : LinearCode (ZMod 2) ι) {dX dZ t : Nat}
    (hminX : MinimumDistance zCode.dual dX)
    (hminZ : MinimumDistance xCode.dual dZ)
    (hbound : 2 * t < min dX dZ)
    {E F : Binary ι}
    (hE : E ∈ scopedByWeight (ι := ι) t)
    (hF : F ∈ scopedByWeight (ι := ι) t)
    (hnontrivial :
      (binaryMul (binaryDagger E) F).vector.xPart ≠ 0 ∨
      (binaryMul (binaryDagger E) F).vector.zPart ≠ 0) :
    syndromeSeparatedByCheckSet (binaryCSSCheckSet xCode zCode) E F := by
  rw [mem_scopedByWeight] at hE hF
  have hmulLe :
      weight (binaryMul (binaryDagger E) F) ≤ t + t := by
    calc
      weight (binaryMul (binaryDagger E) F) ≤ weight (binaryDagger E) + weight F :=
        weight_binaryMul_le (binaryDagger E) F
      _ = weight E + weight F := by
        simp
      _ ≤ t + t :=
        Nat.add_le_add hE hF
  have htt : t + t < min dX dZ := by
    simpa [two_mul] using hbound
  have hwt : weight (binaryMul (binaryDagger E) F) < min dX dZ :=
    lt_of_le_of_lt hmulLe htt
  simpa [syndromeSeparatedByCheckSet] using
    checkDistinguishes_binary_of_weight_lt_dualMinimumDistances
      xCode zCode hminX hminZ hnontrivial hwt
end QEC.Coding.PauliSymplectic
