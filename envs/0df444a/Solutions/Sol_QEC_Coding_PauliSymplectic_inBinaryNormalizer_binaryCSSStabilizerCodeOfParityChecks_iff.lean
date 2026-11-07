-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.inBinaryNormalizer_binaryCSSStabilizerCodeOfParityChecks_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:27:07.360318+00:00
-- url     : https://prove2.me/submissions/a9d34dfb-7f1c-4248-8c63-f0a42e72cb58

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_CSS_Distance
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
open Classical
universe u v
open QEC.Coding.PauliSymplectic
variable {ι κP κQ : Type v} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (E : Binary ι) :
    (binaryCSSStabilizerCodeOfParityChecks P Q horth).InBinaryNormalizer E ↔
      E.vector.xPart ∈ (parityCheckKernelCode P).carrier ∧
      E.vector.zPart ∈ (parityCheckKernelCode Q).carrier := by
  let C := binaryCSSStabilizerCodeOfParityChecks P Q horth
  constructor
  · intro hnormalizer
    constructor
    · rw [← parityCheckRowCode_dual_eq_kernelCode P]
      refine ((parityCheckRowCode P).mem_dual E.vector.xPart).2 ?_
      intro z hz
      have hcheck : cssZCheck z ∈ C.stabilizers := by
        exact Or.inr ⟨z, hz, rfl⟩
      have hgenerated := mem_generatedGroup_of_mem_stabilizers C hcheck
      have hcommutes := hnormalizer (cssZCheck z) hgenerated
      simpa [Commutes, symplecticForm, wordPairing_apply, dotProduct] using hcommutes
    · rw [← parityCheckRowCode_dual_eq_kernelCode Q]
      refine ((parityCheckRowCode Q).mem_dual E.vector.zPart).2 ?_
      intro x hx
      have hcheck : cssXCheck x ∈ C.stabilizers := by
        exact Or.inl ⟨x, hx, rfl⟩
      have hgenerated := mem_generatedGroup_of_mem_stabilizers C hcheck
      have hcommutes := hnormalizer (cssXCheck x) hgenerated
      simpa [Commutes, symplecticForm, wordPairing_apply, dotProduct,
        Finset.sum_neg_distrib] using hcommutes
  · rintro ⟨hxKernel, hzKernel⟩ S hS
    have hxDual : E.vector.xPart ∈ (parityCheckRowCode P).dual.carrier := by
      simpa [parityCheckRowCode_dual_eq_kernelCode P] using hxKernel
    have hzDual : E.vector.zPart ∈ (parityCheckRowCode Q).dual.carrier := by
      simpa [parityCheckRowCode_dual_eq_kernelCode Q] using hzKernel
    have hdual : (parityCheckRowCode P).carrier ≤
        (parityCheckRowCode Q).dual.carrier :=
      (parityCheckRows_orthogonal_iff_rowCode_le_dual P Q).1 horth
    have hcomponents :
        S.vector.xPart ∈ (parityCheckRowCode Q).carrier ∧
        S.vector.zPart ∈ (parityCheckRowCode P).carrier := by
      have hfull :=
        binaryCSSStabilizerCodeOfDualLe_generatedGroup_components
          (parityCheckRowCode Q) (parityCheckRowCode P) hdual
          (P := S) (by
            exact hS)
      exact ⟨hfull.2.1, hfull.2.2⟩
    have hxPair : wordPairing E.vector.xPart S.vector.zPart = 0 :=
      ((parityCheckRowCode P).mem_dual E.vector.xPart).1 hxDual
        S.vector.zPart hcomponents.2
    have hzPair : wordPairing E.vector.zPart S.vector.xPart = 0 :=
      ((parityCheckRowCode Q).mem_dual E.vector.zPart).1 hzDual
        S.vector.xPart hcomponents.1
    simpa [Commutes, symplecticForm, wordPairing_apply, dotProduct] using
      sub_eq_zero.mpr (by
        rw [show (∑ i, E.vector.xPart i * S.vector.zPart i) = 0 by
          simpa [wordPairing_apply, dotProduct] using hxPair]
        rw [show (∑ i, E.vector.zPart i * S.vector.xPart i) = 0 by
          simpa [wordPairing_apply, dotProduct, mul_comm] using hzPair])
end QEC.Coding.PauliSymplectic
