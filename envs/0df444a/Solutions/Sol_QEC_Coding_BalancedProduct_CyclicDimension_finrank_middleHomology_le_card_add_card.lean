-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.CyclicDimension.finrank_middleHomology_le_card_add_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:56:21.791259+00:00
-- url     : https://prove2.me/submissions/82d12c10-1531-4102-993c-898a8fdb89f3

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_boundary1_rank_lowerBound
import Theorems.Thm_QEC_Coding_BalancedProduct_CyclicDimension_boundary2_rank_lowerBound
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicEquiv_apply_eq_generator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicInvEquiv_apply_eq_invGenerator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_A
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_B_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_A
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_B
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_dualData
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inl_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inr_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_swapWord
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_horizontalPart_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_finrank_middleHomology_eq
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockEquiv_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_eq_sub
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_outNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_eq_add
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_inNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inl
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inr
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_ThreeTermChainHomotopyEquiv_finrank_middleHomology_eq
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
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.finCyclicEquiv_apply_eq_generator_pow
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.finCyclicInvEquiv_apply_eq_invGenerator_pow
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.liftedProductData_A
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.liftedProductData_B_apply
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_A
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_B
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_dualData
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inl_apply
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inr_apply
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_swapWord
attribute [local simp] QEC.Coding.BalancedProduct.PKDistance.horizontalPart_apply
attribute [local simp] QEC.Coding.BalancedProduct.PKDistance.verticalPart_apply
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomTwist.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.blockEquiv_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_eq_sub
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_outNeighbor
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_eq_add
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_inNeighbor
attribute [local simp] QEC.Coding.FiberBundle.homologyBaseProjection_add
attribute [local simp] QEC.Coding.FiberBundle.mem_horizontalBoundaryShadow_iff
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inl
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inr
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
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
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.CyclicDimension
open QEC.Coding
universe u
namespace QEC.Coding.BalancedProduct.CyclicDimension
theorem _root_.solution
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q]
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q))) :
    Module.finrank (ZMod 2)
        (LiftedProduct.chainComplex (Cyclic.data q A)).middleHomology ≤
      Fintype.card aCol + Fintype.card aRow := by
  let D := Cyclic.data q A
  let K := LiftedProduct.chainComplex D
  have hBoundaryOne := boundary1_rank_lowerBound q A
  have hBoundaryTwo := boundary2_rank_lowerBound q A
  have hRankNullity := K.boundary1.finrank_range_add_finrank_ker
  have hMiddle : Module.finrank (ZMod 2)
      (Word (ZMod 2) (LiftedProduct.QubitIndex
        aRow aCol Unit Unit (Cyclic.CyclicGroup q))) =
      q * (Fintype.card aCol + Fintype.card aRow) := by
    simp [LiftedProduct.QubitIndex, Cyclic.CyclicGroup, ZMod.card,
      Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc]
  rw [hMiddle] at hRankNullity
  have hCycles : Dimension K.middleCycleCode =
      Module.finrank (ZMod 2) (LinearMap.ker K.boundary1) := by
    rw [Dimension_eq_finrank_carrier]
    rfl
  have hBoundaries : Dimension K.middleBoundaryCode =
      Module.finrank (ZMod 2) (LinearMap.range K.boundary2) := by
    rw [Dimension_eq_finrank_carrier]
    rfl
  rw [K.finrank_middleHomology_eq, hCycles, hBoundaries]
  change _ ≤ Fintype.card aCol + Fintype.card aRow
  change Fintype.card aRow * (q - 1) ≤
    Module.finrank (ZMod 2) (LinearMap.range K.boundary1) at hBoundaryOne
  change Fintype.card aCol * (q - 1) ≤
    Module.finrank (ZMod 2) (LinearMap.range K.boundary2) at hBoundaryTwo
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqSplit : q = q - 1 + 1 := by omega
  have hDimensionSplit :
      q * (Fintype.card aCol + Fintype.card aRow) =
        Fintype.card aRow * (q - 1) +
          Fintype.card aCol * (q - 1) +
            (Fintype.card aCol + Fintype.card aRow) := by
    conv_lhs => rw [hqSplit]
    ring
  omega
end QEC.Coding.BalancedProduct.CyclicDimension
