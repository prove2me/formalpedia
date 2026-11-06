-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.exists_semanticStabilizerDistance_iff_exists_logicalPauli
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:11:01.818269+00:00
-- url     : https://prove2.me/submissions/a79029b9-36eb-4046-b871-1995a7651a38

import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Theorems.Thm_QEC_Coding_StabilizerCode_not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
import Theorems.Thm_QEC_Coding_StabilizerCode_semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
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
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
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
open QEC.Coding.StabilizerCode
universe u
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    (Q : SourceValidBinary ι) :
    (∃ d, SemanticStabilizerDistance Q d) ↔
      ∃ E, Q.1.InBinaryNormalizer E ∧
        ¬ Q.1.InGeneratedGroupUpToSign E := by
  constructor
  · rintro ⟨d, E, hNondetectable, _hWeight, _hLeast⟩
    exact ⟨E,
      (not_detectableOn_toQubitOperator_iff_inBinaryNormalizer_and_not_inGeneratedGroupUpToSign
        Q E).1 hNondetectable⟩
  · rintro ⟨E, hNormalizer, hOutsideGenerated⟩
    classical
    let logicalPaulis : Finset (Binary ι) :=
      Finset.univ.filter fun P =>
        Q.1.InBinaryNormalizer P ∧ ¬ Q.1.InGeneratedGroupUpToSign P
    have hNonempty : logicalPaulis.Nonempty := by
      exact ⟨E, by simp [logicalPaulis, hNormalizer, hOutsideGenerated]⟩
    obtain ⟨P, hP, hMinimum⟩ :=
      Finset.exists_min_image logicalPaulis (fun A : Binary ι => weight A) hNonempty
    have hPNormalizer : Q.1.InBinaryNormalizer P :=
      (Finset.mem_filter.mp hP).2.1
    have hPOutsideGenerated : ¬ Q.1.InGeneratedGroupUpToSign P :=
      (Finset.mem_filter.mp hP).2.2
    refine ⟨weight P,
      (semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff Q (weight P)).2
        ⟨P, hPNormalizer, hPOutsideGenerated, rfl, ?_⟩⟩
    intro F hFNormalizer hFOutsideGenerated
    exact hMinimum F (by simp [logicalPaulis, hFNormalizer, hFOutsideGenerated])
end QEC.Coding.StabilizerCode
