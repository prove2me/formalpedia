-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.finrank_middleHomology_eq_dimension_products
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:51:19.089199+00:00
-- url     : https://prove2.me/submissions/0c5be86b-d950-4096-97ac-e663b1d29ba0

import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_BoundaryMaps
import Definitions.Def_QEC_Coding_HypergraphProduct_Dimension_Formula
import Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_ker_boundary1Transpose_eq
import Theorems.Thm_QEC_Coding_HypergraphProduct_finrank_ker_boundary2_eq
import Theorems.Thm_P2M_QEC_Coding_HypergraphProduct_finrank_range_wordLinearMapTranspose_toLin__eq_b35987ba4f3b
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_xCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_binaryCSSCode_zCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary1
import Theorems.Thm_QEC_Coding_HypergraphProduct_chainComplex_boundary2
import Theorems.Thm_QEC_Coding_HypergraphProduct_first_dimension_add_rows_eq_cols_add_transpose_dimension
import Theorems.Thm_QEC_Coding_HypergraphProduct_jointTensorWordMap_tmul_fst_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_jointTensorWordMap_tmul_snd_apply
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_firstTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_mem_secondTransposeCode_iff
import Theorems.Thm_QEC_Coding_HypergraphProduct_second_dimension_add_rows_eq_cols_add_transpose_dimension
import Theorems.Thm_QEC_Coding_HypergraphProduct_wordTensorEquiv_tmul_apply
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
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
attribute [local simp] QEC.Coding.HypergraphProduct.jointTensorWordMap_tmul_fst_apply
attribute [local simp] QEC.Coding.HypergraphProduct.jointTensorWordMap_tmul_snd_apply
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_firstTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.mem_secondTransposeCode_iff
attribute [local simp] QEC.Coding.HypergraphProduct.wordTensorEquiv_tmul_apply
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
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
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo) :
    Module.finrank (ZMod 2) (chainComplex D).middleHomology =
      Dimension (firstCode D) * Dimension (secondCode D) +
        Dimension (firstTransposeCode D) *
          Dimension (secondTransposeCode D) := by
  have hHomRaw := Submodule.finrank_quotient_add_finrank
    (chainComplex D).middleBoundaryInCycles
  rw [(chainComplex D).finrank_middleBoundaryInCycles_eq] at hHomRaw
  have hHom :
      Module.finrank (ZMod 2) (chainComplex D).middleHomology +
          Module.finrank (ZMod 2) (LinearMap.range (boundary2 D)) =
        Module.finrank (ZMod 2) (LinearMap.ker (boundary1 D)) := by
    exact hHomRaw
  have hBoundary1 := (boundary1 D).finrank_range_add_finrank_ker
  have hBoundary1Transpose :=
    (wordLinearMapTranspose (boundary1 D)).finrank_range_add_finrank_ker
  have hBoundary2 := (boundary2 D).finrank_range_add_finrank_ker
  have hBoundary1Size :
      Module.finrank (ZMod 2) (LinearMap.range (boundary1 D)) +
          Module.finrank (ZMod 2) (LinearMap.ker (boundary1 D)) =
        Fintype.card colOne * Fintype.card colTwo +
          Fintype.card rowOne * Fintype.card rowTwo := by
    simpa [Length, QubitIndex] using hBoundary1
  have hBoundary1TransposeSize :
      Module.finrank (ZMod 2)
          (LinearMap.range (wordLinearMapTranspose (boundary1 D))) +
        Module.finrank (ZMod 2)
          (LinearMap.ker (wordLinearMapTranspose (boundary1 D))) =
        Fintype.card rowOne * Fintype.card colTwo := by
    simpa [Length, C0Index] using hBoundary1Transpose
  have hBoundary2Size :
      Module.finrank (ZMod 2) (LinearMap.range (boundary2 D)) +
          Module.finrank (ZMod 2) (LinearMap.ker (boundary2 D)) =
        Fintype.card colOne * Fintype.card rowTwo := by
    simpa [Length, C2Index] using hBoundary2
  have hBoundary1Rank :
      Module.finrank (ZMod 2)
          (LinearMap.range (wordLinearMapTranspose (boundary1 D))) =
        Module.finrank (ZMod 2) (LinearMap.range (boundary1 D)) := by
    exact finrank_range_wordLinearMapTranspose_toLin'_eq (boundary1Matrix D)
  have hEndpointOne := finrank_ker_boundary1Transpose_eq D
  have hEndpointTwo := finrank_ker_boundary2_eq D
  have hFirstRelation :=
    first_dimension_add_rows_eq_cols_add_transpose_dimension D
  have hSecondRelation :=
    second_dimension_add_rows_eq_cols_add_transpose_dimension D
  nlinarith
end QEC.Coding.HypergraphProduct
