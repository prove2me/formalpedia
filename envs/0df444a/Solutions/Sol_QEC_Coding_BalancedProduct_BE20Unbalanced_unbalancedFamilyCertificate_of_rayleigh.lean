-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.BE20Unbalanced.unbalancedFamilyCertificate_of_rayleigh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:09:36.072331+00:00
-- url     : https://prove2.me/submissions/21d92bee-5bbf-41b6-afc2-27b648905de3

import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_quotientScales_large
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_dimension_power_bounds
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_dressedX_power_bound
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_dressedZ_linear_bounds
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicEquiv_apply_eq_generator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicInvEquiv_apply_eq_invGenerator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_A
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_B_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_freeOrbitEquiv_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_freeOrbitEquiv_symm_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_groupAlgebraMatrix_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_lpsHorizontalSubsystem_blocklength_eq_polynomial
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_lpsHorizontalSubsystem_logicalQubits_lowerBound_polynomial
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSFamily_lpsHorizontalSubsystem_logicalQubits_upperBound_polynomial
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsHorizontalSubsystem_boundedLocality
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSQuotientTanner_lpsHorizontalSubsystem_dressedDistanceBounds
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_checkBlock_basis_same
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_incidentAsEdge_edgeAsIncident
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_A
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_B
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_dualData
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inl_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inr_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_swapWord
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_horizontalPart_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_apply
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
import Theorems.Thm_QEC_Coding_FiberBundle_binaryCSSCode_stabilizer_isSourceValidBinary
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inl
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inr
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_binaryCSSCode_stabilizer_isSourceValidBinary
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
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
attribute [local simp] QEC.Coding.BalancedProduct.FreeOrbitCoordinates.freeOrbitEquiv_apply
attribute [local simp] QEC.Coding.BalancedProduct.FreeOrbitCoordinates.freeOrbitEquiv_symm_apply
attribute [local simp] QEC.Coding.BalancedProduct.FreeOrbitCoordinates.groupAlgebraMatrix_apply
attribute [local simp] QEC.Coding.BalancedProduct.LPSTanner.checkBlock_basis_same
attribute [local simp] QEC.Coding.BalancedProduct.LPSTanner.incidentAsEdge_edgeAsIncident
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
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Unbalanced
open QEC.Coding
open LPSFamily LPSGraph LPSQuotientTanner
namespace QEC.Coding.BalancedProduct.BE20Unbalanced
theorem _root_.solution
    (q : Nat) [Fact q.Prime]
    (hqLarge : familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    UnbalancedFamilyCertificate q (by
      dsimp [familyThreshold] at hqLarge
      omega) hq := by
  classical
  have hq40 : 40 < q := by
    dsimp [familyThreshold] at hqLarge
    omega
  have hq804 : 804 ≤ q := by
    dsimp [familyThreshold] at hqLarge
    omega
  have hScales := quotientScales_large q hq40 hqLarge hq
  let hOdd : Odd q :=
    (Fact.out : q.Prime).odd_of_ne_two (by omega)
  let D := HorizontalSubsystem.horizontalSubsystem
    (lpsTannerGroupAlgebraMatrix q hq40 hq)
    (Cyclic.cyclicGenerator q)
    (by simpa [Cyclic.CyclicGroup, ZMod.card] using hOdd)
  let N := Fintype.card
    (LiftedProduct.QubitIndex
      (CheckOrbit401 q) (EdgeOrbit401 q hq) Unit Unit
      (Cyclic.CyclicGroup q))
  let K := D.logicalQubits
  let dX := lpsDressedXLowerBound q
  let dZ := lpsDressedZLowerBound q hq
  have hDistances := lpsHorizontalSubsystem_dressedDistanceBounds
    q hq40 hq804 hq hLPS hScales.1 hScales.2
  have hN : N = 401 * q * (q ^ 2 - 1) :=
    LPSFamily.lpsHorizontalSubsystem_blocklength_eq_polynomial q hq40 hq
  have hKLower : q ^ 2 - 1 ≤ K :=
    LPSFamily.lpsHorizontalSubsystem_logicalQubits_lowerBound_polynomial
      q hq40 hq
  have hKUpper : K ≤ 201 * (q ^ 2 - 1) :=
    LPSFamily.lpsHorizontalSubsystem_logicalQubits_upperBound_polynomial
      q hq40 hq
  have hDimension := dimension_power_bounds q N K hqLarge hN hKLower hKUpper
  have hXPower := dressedX_power_bound q N hq40 hqLarge hq hN
  have hZLinear := dressedZ_linear_bounds q N hq40 hqLarge hq hN
  unfold UnbalancedFamilyCertificate
  dsimp only
  exact ⟨ChainComplexData.binaryCSSCode_stabilizer_isSourceValidBinary D.complex,
    hDistances.2, hDistances.1,
    lpsHorizontalSubsystem_boundedLocality q hq40 hq,
    hN, hKLower, hKUpper, hDimension.1, hDimension.2,
    hXPower, hZLinear.1, hZLinear.2⟩
end QEC.Coding.BalancedProduct.BE20Unbalanced
