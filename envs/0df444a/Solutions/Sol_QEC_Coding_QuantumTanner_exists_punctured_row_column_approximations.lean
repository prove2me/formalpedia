-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_punctured_row_column_approximations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:08:21.254419+00:00
-- url     : https://prove2.me/submissions/b42e996b-c8bc-4b21-9aa6-eca35c867f61

import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_punctureMap_le
import Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_matrix_eq_sum_rows
import Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_matrix_eq_sum_columns
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_blockLength
import Theorems.Thm_QEC_Coding_QuantumTanner_Family_ofData_encodedDimension
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localExtension_apply_link
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_localRestriction_localExtension
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
import Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Coding.QuantumTanner.Data.blockLength_eq
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_blockLength
attribute [local simp] QEC.Coding.QuantumTanner.Family.ofData_encodedDimension
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localExtension_apply_link
attribute [local simp] QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.localRestriction_localExtension
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
attribute [local simp] QEC.QLDPC.QuantumCodeFamily.blockLength_eq_card
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (removedA : Finset A) (removedB : Finset B)
    (x : Word (ZMod 2) (A × B)) (rowError columnError : Nat)
    (hRows : ∀ a : KeptCoordinate removedA, ∃ r : Word (ZMod 2) B,
      r ∈ CB.carrier ∧ HammingWeight (rowRestriction a.1 x + r) ≤ rowError)
    (hColumns : ∀ b : KeptCoordinate removedB, ∃ c : Word (ZMod 2) A,
      c ∈ CA.carrier ∧ HammingWeight (columnRestriction b.1 x + c) ≤ columnError) :
    ∃ C R : Word (ZMod 2) (KeptCoordinate removedA × KeptCoordinate removedB),
      C ∈ (columnCode (puncturedCode CA removedA)).carrier ∧
      R ∈ (rowCode (puncturedCode CB removedB)).carrier ∧
      HammingWeight (tensorPunctureMap removedA removedB x + C) ≤
        Fintype.card B * columnError ∧
      HammingWeight (tensorPunctureMap removedA removedB x + R) ≤
        Fintype.card A * rowError := by
  choose rowWord hRowMem hRowClose using hRows
  choose columnWord hColumnMem hColumnClose using hColumns
  let R : Word (ZMod 2) (KeptCoordinate removedA × KeptCoordinate removedB) :=
    fun ab => rowWord ab.1 ab.2.1
  let C : Word (ZMod 2) (KeptCoordinate removedA × KeptCoordinate removedB) :=
    fun ab => columnWord ab.2 ab.1.1
  have hR : R ∈ (rowCode (puncturedCode CB removedB)).carrier := by
    intro a
    exact (mem_puncturedCode CB removedB _).mpr ⟨rowWord a, hRowMem a, rfl⟩
  have hC : C ∈ (columnCode (puncturedCode CA removedA)).carrier := by
    intro b
    exact (mem_puncturedCode CA removedA _).mpr ⟨columnWord b, hColumnMem b, rfl⟩
  have hColumnError (b : KeptCoordinate removedB) :
      HammingWeight (columnRestriction b (tensorPunctureMap removedA removedB x + C)) ≤
        columnError := by
    have hSame : columnRestriction b (tensorPunctureMap removedA removedB x + C) =
        punctureMap removedA (columnRestriction b.1 x + columnWord b) := by
      ext a
      rfl
    rw [hSame]
    exact (hammingWeight_punctureMap_le removedA _).trans (hColumnClose b)
  have hRowError (a : KeptCoordinate removedA) :
      HammingWeight (rowRestriction a (tensorPunctureMap removedA removedB x + R)) ≤
        rowError := by
    have hSame : rowRestriction a (tensorPunctureMap removedA removedB x + R) =
        punctureMap removedB (rowRestriction a.1 x + rowWord a) := by
      ext b
      rfl
    rw [hSame]
    exact (hammingWeight_punctureMap_le removedB _).trans (hRowClose a)
  refine ⟨C, R, hC, hR, ?_, ?_⟩
  · calc
      HammingWeight (tensorPunctureMap removedA removedB x + C) =
          ∑ b : KeptCoordinate removedB,
            HammingWeight (columnRestriction b (tensorPunctureMap removedA removedB x + C)) :=
        hammingWeight_matrix_eq_sum_columns _
      _ ≤ ∑ _b : KeptCoordinate removedB, columnError :=
        Finset.sum_le_sum fun b _ => hColumnError b
      _ = Fintype.card (KeptCoordinate removedB) * columnError := by simp
      _ ≤ Fintype.card B * columnError :=
        Nat.mul_le_mul_right _ (Fintype.card_subtype_le _)
  · calc
      HammingWeight (tensorPunctureMap removedA removedB x + R) =
          ∑ a : KeptCoordinate removedA,
            HammingWeight (rowRestriction a (tensorPunctureMap removedA removedB x + R)) :=
        hammingWeight_matrix_eq_sum_rows _
      _ ≤ ∑ _a : KeptCoordinate removedA, rowError :=
        Finset.sum_le_sum fun a _ => hRowError a
      _ = Fintype.card (KeptCoordinate removedA) * rowError := by simp
      _ ≤ Fintype.card A * rowError :=
        Nat.mul_le_mul_right _ (Fintype.card_subtype_le _)
end QEC.Coding.QuantumTanner
