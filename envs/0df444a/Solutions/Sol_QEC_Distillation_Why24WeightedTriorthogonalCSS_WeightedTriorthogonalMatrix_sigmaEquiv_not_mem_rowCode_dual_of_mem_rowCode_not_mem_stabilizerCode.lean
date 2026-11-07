-- Prove2me | solution 1 for QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix.sigmaEquiv_not_mem_rowCode_dual_of_mem_rowCode_not_mem_stabilizerCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:08:11.403242+00:00
-- url     : https://prove2.me/submissions/e282536a-87a8-478d-9e5b-34d5b23b19f9

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_QuditQubitConversion_U7Gate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
import Theorems.Thm_QEC_Distillation_Why24WeightedTriorthogonalCSS_WeightedTriorthogonalMatrix_wordPairing_sigmaEquiv
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_taggedCczTransport_apply
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
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_xCode
attribute [local simp] QEC.Coding.HypergraphProduct.binaryCSSCode_zCode
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary1
attribute [local simp] QEC.Coding.HypergraphProduct.chainComplex_boundary2
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Coding.why24U_apply
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_apply
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.taggedCczTransport_apply
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
open QEC QEC.Distillation QEC.Distillation.Why24WeightedTriorthogonalCSS
open QEC.Coding QEC.Semantics
open scoped BigOperators
open QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
variable {Logical Stabilizer Site : Type}
variable [Fintype Logical] [DecidableEq Logical]
variable [Fintype Stabilizer] [DecidableEq Stabilizer]
variable [Fintype Site] [DecidableEq Site]
namespace QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
theorem _root_.solution
    (R : WeightedTriorthogonalMatrix Logical Stabilizer Site)
    {x : Why24Word Site} (hx : x ∈ R.rowCode.carrier)
    (hxOutside : x ∉ R.stabilizerCode.carrier) :
    R.sigmaEquiv x ∉ R.rowCode.dual.carrier := by
  classical
  intro hxDual
  obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun F1024).mp hx
  change R.combinedWord q = x at hq
  have hlogical : ∀ a : Logical, q (Sum.inl a) = 0 := by
    intro a
    have horth := R.rowCode.orthogonal_of_mem_dual hxDual
      (Submodule.subset_span ⟨Sum.inl a, rfl⟩)
    rw [R.wordPairing_sigmaEquiv] at horth
    change weightedPairing R.sigma x (R.logicalRow a) = 0 at horth
    have hpair :
        weightedPairing R.sigma (R.combinedWord q) (R.logicalRow a) =
          q (Sum.inl a) * R.tau a := by
      unfold combinedWord
      change weightedPairingLeftLinearMap R.sigma (R.logicalRow a)
          (∑ r, q r • R.row r) = _
      rw [map_sum]
      simp only [map_smul, weightedPairingLeftLinearMap_apply, smul_eq_mul]
      rw [Fintype.sum_sum_type]
      simp only [row_inl, row_inr]
      have hstabilizer :
          (∑ s : Stabilizer,
            q (Sum.inr s) * weightedPairing R.sigma (R.stabilizerRow s)
              (R.logicalRow a)) = 0 := by
        apply Finset.sum_eq_zero
        intro s _
        have h := R.weighted_condition (Sum.inr s) (Sum.inl a)
        have hzero : weightedPairing R.sigma (R.stabilizerRow s) (R.logicalRow a) = 0 := by
          simpa [weightedTarget] using h
        rw [hzero, mul_zero]
      rw [hstabilizer, add_zero]
      have hlogicalSum := R.weightedPairing_logicalWord_logicalRow
        (fun b => q (Sum.inl b)) a
      change weightedPairingLeftLinearMap R.sigma (R.logicalRow a)
          (∑ b, q (Sum.inl b) • R.logicalRow b) =
        q (Sum.inl a) * R.tau a at hlogicalSum
      rw [map_sum] at hlogicalSum
      simpa only [map_smul, weightedPairingLeftLinearMap_apply, smul_eq_mul] using hlogicalSum
    rw [← hq, hpair] at horth
    exact (mul_eq_zero.mp horth).resolve_right (R.tau_ne_zero a)
  apply hxOutside
  rw [← hq]
  have hsplit :
      R.combinedWord q =
        (∑ a : Logical, q (Sum.inl a) • R.logicalRow a) +
          ∑ s : Stabilizer, q (Sum.inr s) • R.stabilizerRow s := by
    simp [combinedWord, row, Fintype.sum_sum_type]
  rw [hsplit]
  have hzero : (∑ a : Logical, q (Sum.inl a) • R.logicalRow a) = 0 := by
    simp [hlogical]
  rw [hzero, zero_add]
  exact Submodule.sum_mem R.stabilizerCode.carrier
    (fun s _ => R.stabilizerCode.carrier.smul_mem _
      (Submodule.subset_span ⟨s, rfl⟩))
end QEC.Distillation.Why24WeightedTriorthogonalCSS.WeightedTriorthogonalMatrix
