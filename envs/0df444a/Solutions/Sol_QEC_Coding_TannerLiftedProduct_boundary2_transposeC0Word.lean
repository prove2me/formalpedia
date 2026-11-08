-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.boundary2_transposeC0Word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:50:28.92248+00:00
-- url     : https://prove2.me/submissions/aa689135-8152-433b-ab7d-021506d2096f

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProductDuality
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerTranspose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_boundary1_transposeTannerWord_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_inverseLabels_symm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_wordPairing_transposeTannerWord
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_wordPairing_transposeC0Word
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_dualData_A
import Theorems.Thm_QEC_Coding_LiftedProduct_dualData_B
import Theorems.Thm_QEC_Coding_LiftedProduct_dualData_dualData
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_inl_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_inr_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_neg
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_signedSwapWord
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_signedUnswapWord
import Theorems.Thm_QEC_Coding_LiftedProduct_signedUnswapWord_signedSwapWord
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalNeighbor_horizontalNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_symm_apply
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.LiftedProduct.dualData_A
attribute [local simp] QEC.Coding.LiftedProduct.dualData_B
attribute [local simp] QEC.Coding.LiftedProduct.dualData_dualData
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_inl_apply
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_inr_apply
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_neg
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_signedSwapWord
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_signedUnswapWord
attribute [local simp] QEC.Coding.LiftedProduct.signedUnswapWord_signedSwapWord
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Coding.TannerLiftedProduct.horizontalNeighbor_horizontalNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_symm_apply
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
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
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label targetLabel : W → G) (inverseDirection : W ≃ W)
    (hInverse : ∀ a, targetLabel (inverseDirection a) = (label a)⁻¹)
    (h : Matrix R W F) (h' : Matrix R' W F)
    (x : Word F (LiftedProduct.C0Index (Fin 2 × R) W G)) :
    LiftedProduct.boundary2
        (data targetLabel (reindexColumns inverseDirection h')
          (reindexColumns inverseDirection h))
        (transposeC0Word inverseDirection x) =
      transposeTannerWord inverseDirection
        (wordLinearMapTranspose (LiftedProduct.boundary1 (data label h h')) x) := by
  classical
  rw [← sub_eq_zero]
  apply (wordPairing_nondegenerate (F := F)).right
  intro y
  have hInverseSymm := inverseLabels_symm
    label targetLabel inverseDirection hInverse
  have hCoordinate :
      (fun c0 =>
        wordLinearMapTranspose
          (LiftedProduct.boundary2
            (data targetLabel (reindexColumns inverseDirection h')
              (reindexColumns inverseDirection h))) y
          ((transposeEdgeEquiv inverseDirection.symm).symm c0)) =
        LiftedProduct.boundary1 (data label h h')
          (transposeTannerWord inverseDirection.symm y) := by
    funext c0
    obtain ⟨c2, rfl⟩ :=
      (transposeEdgeEquiv inverseDirection.symm).surjective c0
    simp only [Equiv.symm_apply_apply]
    symm
    simpa using boundary1_transposeTannerWord_apply
      targetLabel label inverseDirection.symm
      hInverseSymm (reindexColumns inverseDirection h')
      (reindexColumns inverseDirection h) y c2
  have hPair :
      wordPairing y
          (LiftedProduct.boundary2
            (data targetLabel (reindexColumns inverseDirection h')
              (reindexColumns inverseDirection h))
            (transposeC0Word inverseDirection x)) =
        wordPairing y
          (transposeTannerWord inverseDirection
            (wordLinearMapTranspose
              (LiftedProduct.boundary1 (data label h h')) x)) := by
    calc
      wordPairing y
          (LiftedProduct.boundary2
            (data targetLabel (reindexColumns inverseDirection h')
              (reindexColumns inverseDirection h))
            (transposeC0Word inverseDirection x)) =
          wordPairing
            (wordLinearMapTranspose
              (LiftedProduct.boundary2
                (data targetLabel (reindexColumns inverseDirection h')
                  (reindexColumns inverseDirection h))) y)
            (transposeC0Word inverseDirection x) := by
              exact (wordPairing_wordLinearMapTranspose
                (LiftedProduct.boundary2
                  (data targetLabel (reindexColumns inverseDirection h')
                    (reindexColumns inverseDirection h))) y
                (transposeC0Word inverseDirection x)).symm
      _ = wordPairing (transposeC0Word inverseDirection x)
            (wordLinearMapTranspose
              (LiftedProduct.boundary2
                (data targetLabel (reindexColumns inverseDirection h')
                  (reindexColumns inverseDirection h))) y) := by
              simp [wordPairing_apply, dotProduct_comm]
      _ = wordPairing x
            (fun c0 =>
              wordLinearMapTranspose
                (LiftedProduct.boundary2
                  (data targetLabel (reindexColumns inverseDirection h')
                    (reindexColumns inverseDirection h))) y
                ((transposeEdgeEquiv inverseDirection.symm).symm c0)) :=
              wordPairing_transposeC0Word inverseDirection x _
      _ = wordPairing x
            (LiftedProduct.boundary1 (data label h h')
              (transposeTannerWord inverseDirection.symm y)) := by
              rw [hCoordinate]
      _ = wordPairing
            (wordLinearMapTranspose
              (LiftedProduct.boundary1 (data label h h')) x)
            (transposeTannerWord inverseDirection.symm y) := by
              exact (wordPairing_wordLinearMapTranspose
                (LiftedProduct.boundary1 (data label h h')) x
                (transposeTannerWord inverseDirection.symm y)).symm
      _ = wordPairing
            (transposeTannerWord inverseDirection
              (wordLinearMapTranspose
                (LiftedProduct.boundary1 (data label h h')) x)) y := by
              exact (wordPairing_transposeTannerWord inverseDirection _ y).symm
      _ = wordPairing y
            (transposeTannerWord inverseDirection
              (wordLinearMapTranspose
                (LiftedProduct.boundary1 (data label h h')) x)) := by
              simp [wordPairing_apply, dotProduct_comm]
  simpa [wordPairing_apply, dotProduct_sub] using sub_eq_zero.mpr hPair
end QEC.Coding.TannerLiftedProduct
