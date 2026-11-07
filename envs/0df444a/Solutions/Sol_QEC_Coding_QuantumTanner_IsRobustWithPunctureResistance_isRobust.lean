-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.IsRobustWithPunctureResistance.isRobust
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:08:55.129802+00:00
-- url     : https://prove2.me/submissions/98697db2-70e6-4421-abc2-eae85d64bce5

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_RobustnessTransport
import Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_comp_equiv
import Theorems.Thm_QEC_Coding_QuantumTanner_minimumDistance_punctured_empty
import Theorems.Thm_QEC_Coding_QuantumTanner_dualTensorCode_mem_punctured_empty
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_QuantumTanner_Data_blockLength_eq
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
attribute [local simp] QEC.Coding.QuantumTanner.Data.blockLength_eq
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
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
namespace QEC.Coding.QuantumTanner
namespace IsRobustWithPunctureResistance
theorem _root_.solution
    {A B : Type v} [Fintype A] [Fintype B]
    {CA : LinearCode (ZMod 2) A} {CB : LinearCode (ZMod 2) B}
    {w p : Nat} (h : IsRobustWithPunctureResistance CA CB w p) :
    IsRobust CA CB w := by
  intro dA dB hA hB x hx hweight
  let y : Word (ZMod 2)
      (KeptCoordinate (∅ : Finset A) × KeptCoordinate (∅ : Finset B)) :=
    fun ab => x (ab.1.1, ab.2.1)
  have hw : HammingWeight y = HammingWeight x :=
    hammingWeight_comp_equiv
      ((emptyKeptCoordinateEquiv A).prodCongr (emptyKeptCoordinateEquiv B)) x
  obtain ⟨rows, columns, hcover, hrows, hcolumns⟩ :=
    h ∅ ∅ rfl (Nat.zero_le p) dA dB
      (minimumDistance_punctured_empty CA hA) (minimumDistance_punctured_empty CB hB)
      y (dualTensorCode_mem_punctured_empty CA CB x hx) (hw ▸ hweight)
  refine ⟨rows.image Subtype.val, columns.image Subtype.val, ?_, ?_, ?_⟩
  · intro ab hab
    have hy : (⟨ab.1, by simp⟩, ⟨ab.2, by simp⟩) ∈ hammingSupport y := by
      simpa only [hammingSupport, Finset.mem_filter, Finset.mem_univ, true_and, y] using hab
    have hc := hcover hy
    simp only [Finset.mem_union, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ,
      and_true, true_and] at hc ⊢
    exact hc.elim
      (fun ha => Or.inl (Finset.mem_image.mpr
        ⟨(⟨ab.1, by simp⟩ : KeptCoordinate (∅ : Finset A)), ha, rfl⟩))
      (fun hb => Or.inr (Finset.mem_image.mpr
        ⟨(⟨ab.2, by simp⟩ : KeptCoordinate (∅ : Finset B)), hb, rfl⟩))
  · exact Finset.card_image_le.trans (hw ▸ hrows)
  · exact Finset.card_image_le.trans (hw ▸ hcolumns)
end IsRobustWithPunctureResistance
end QEC.Coding.QuantumTanner
