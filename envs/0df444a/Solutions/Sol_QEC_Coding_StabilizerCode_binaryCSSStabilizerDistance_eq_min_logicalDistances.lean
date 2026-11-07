-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.binaryCSSStabilizerDistance_eq_min_logicalDistances
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:34:56.888743+00:00
-- url     : https://prove2.me/submissions/14da3299-17a9-4b7f-8011-005d11a341a9

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_CSS_Distance
import Theorems.Thm_QEC_Coding_PauliSymplectic_inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
import Theorems.Thm_QEC_Coding_PauliSymplectic_inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_hammingWeight_xPart_le_weight
import Theorems.Thm_QEC_Coding_PauliSymplectic_hammingWeight_zPart_le_weight
import Theorems.Thm_QEC_Coding_StabilizerCode_semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff
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
open Classical
universe u v
open QEC.Coding.StabilizerCode
open PauliSymplectic
variable {ι κP κQ : Type v} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {dX dZ : Nat}
    (hX : CSSXLogicalMinimumDistance P Q dX)
    (hZ : CSSZLogicalMinimumDistance P Q dZ) :
    SemanticStabilizerDistance
      (binaryCSSSourceValidStabilizerOfParityChecks P Q horth) (min dX dZ) := by
  rw [semanticStabilizerDistance_iff_minWeight_inBinaryNormalizer_diff]
  rcases hX with ⟨x, hxKernel, hxOutside, hxWeight, hxLeast⟩
  rcases hZ with ⟨z, hzKernel, hzOutside, hzWeight, hzLeast⟩
  rcases le_total dX dZ with hXZ | hZX
  · refine ⟨cssXCheck x, ?_, ?_, ?_, ?_⟩
    · exact
        (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (cssXCheck x)).2
          ⟨hxKernel, (parityCheckKernelCode Q).carrier.zero_mem⟩
    · intro hgenerated
      have hcomponents :=
        (inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (cssXCheck x)).1 hgenerated
      exact hxOutside hcomponents.1
    · simpa [Nat.min_eq_left hXZ] using
        (weight_cssXCheck_eq_hammingWeight x).trans hxWeight
    · intro F hnormalizer houtside
      have hnormalizerComponents :=
        (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth F).1 hnormalizer
      have houtsideComponents :
          F.vector.xPart ∉ (parityCheckRowCode Q).carrier ∨
          F.vector.zPart ∉ (parityCheckRowCode P).carrier := by
        by_contra hnot
        push Not at hnot
        exact houtside
          ((inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
            P Q horth F).2 hnot)
      rw [Nat.min_eq_left hXZ]
      rcases houtsideComponents with hxF | hzF
      · exact (hxLeast F.vector.xPart hnormalizerComponents.1 hxF).trans
          (hammingWeight_xPart_le_weight F)
      · exact hXZ.trans ((hzLeast F.vector.zPart hnormalizerComponents.2 hzF).trans
          (hammingWeight_zPart_le_weight F))
  · refine ⟨cssZCheck z, ?_, ?_, ?_, ?_⟩
    · exact
        (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (cssZCheck z)).2
          ⟨(parityCheckKernelCode P).carrier.zero_mem, hzKernel⟩
    · intro hgenerated
      have hcomponents :=
        (inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth (cssZCheck z)).1 hgenerated
      exact hzOutside hcomponents.2
    · simpa [Nat.min_eq_right hZX] using
        (weight_cssZCheck_eq_hammingWeight z).trans hzWeight
    · intro F hnormalizer houtside
      have hnormalizerComponents :=
        (inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
          P Q horth F).1 hnormalizer
      have houtsideComponents :
          F.vector.xPart ∉ (parityCheckRowCode Q).carrier ∨
          F.vector.zPart ∉ (parityCheckRowCode P).carrier := by
        by_contra hnot
        push Not at hnot
        exact houtside
          ((inGeneratedGroupUpToSign_binaryCSSStabilizerCodeOfParityChecks_iff
            P Q horth F).2 hnot)
      rw [Nat.min_eq_right hZX]
      rcases houtsideComponents with hxF | hzF
      · exact hZX.trans ((hxLeast F.vector.xPart hnormalizerComponents.1 hxF).trans
          (hammingWeight_xPart_le_weight F))
      · exact (hzLeast F.vector.zPart hnormalizerComponents.2 hzF).trans
          (hammingWeight_zPart_le_weight F)
end QEC.Coding.StabilizerCode
