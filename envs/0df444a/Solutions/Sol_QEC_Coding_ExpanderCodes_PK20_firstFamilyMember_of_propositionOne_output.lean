-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.firstFamilyMember_of_propositionOne_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:31:37.304429+00:00
-- url     : https://prove2.me/submissions/95646032-af66-487b-81c2-4a593d303eb5

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_finite_distance_locality_of_relativeExpansion
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_finrank_middleHomology_bounds
import Theorems.Thm_QEC_Coding_ExpanderCodes_PK20_middleCohomologyDistanceAtMost_lift
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_card_qubitIndex
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
import Theorems.Thm_QEC_Coding_FiberBundle_card_qubitIndex
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inl
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inr
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_card_qubitIndex
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


section
namespace QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
private theorem one_le_of_pos {a : Nat} (ha : 0 < a) : 1 ≤ a := ha
end QEC.Coding.ExpanderCodes.PK20
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
namespace QEC.Coding.ExpanderCodes.PK20
theorem _root_.solution
    (w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m : Nat)
    [NeZero q]
    (A : Matrix (Fin m) (Fin (w * n))
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (hw4 : 4 ≤ w)
    (hgamma : 0 < gamma)
    (hRadiusNumerator : 0 < radiusNumerator)
    (hRadiusDenominator : 0 < radiusDenominator)
    (hExpansionNumerator : 0 < expansionNumerator)
    (hExpansionDenominator : 0 < expansionDenominator)
    (hqOdd : Odd q)
    (hm : m = 2 * (w / 4) * n)
    (hnLower : gamma * Nat.log 2 q ≤ n)
    (hnUpper : n ≤ gamma * (Nat.log 2 q + 1))
    (hDenominatorLeN : radiusDenominator ≤ n)
    (hLiftLarge : 2 * w * radiusDenominator ≤ q)
    (hForwardWeight : ∀ i : Fin (w * n) × Cyclic.CyclicGroup q,
      HammingWeight (PKDistance.tannerAction A (Pi.single i 1)) ≤ w)
    (hTransposeWeight : ∀ i : Fin m × Cyclic.CyclicGroup q,
      HammingWeight
        (PKDistance.tannerAction (LiftedProduct.starTranspose A)
          (Pi.single i 1)) ≤ w)
    (hForwardRelative :
      (PKDistance.tannerAction A).SmallSetExpandingAtRelativeRadius
        radiusNumerator radiusDenominator
        expansionNumerator expansionDenominator)
    (hTransposeRelative :
      (PKDistance.tannerAction
        (LiftedProduct.starTranspose A)).SmallSetExpandingAtRelativeRadius
          radiusNumerator radiusDenominator
          expansionNumerator expansionDenominator) :
    FirstFamilyMember w gamma radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator q n m A := by
  have hqTwo : 2 ≤ q := by
    have hwOne : 1 ≤ w := one_le_of_pos (lt_of_lt_of_le (by norm_num) hw4)
    have hDenominatorOne : 1 ≤ radiusDenominator := one_le_of_pos hRadiusDenominator
    exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hwOne) hDenominatorOne).trans
      hLiftLarge
  have hLogPositive : 0 < Nat.log 2 q := by
    exact Nat.log_pos (by norm_num) hqTwo
  have hnPositive : 0 < n := by
    have := Nat.mul_pos hgamma hLogPositive
    omega
  have hwPositive : 0 < w := lt_of_lt_of_le (by norm_num) hw4
  have hwDiv : 1 ≤ w / 4 := Nat.le_div_iff_mul_le (by norm_num) |>.2 (by simpa using hw4)
  have hmPositive : 0 < m := by
    rw [hm]
    positivity
  have hDenominatorLeM : radiusDenominator ≤ m := by
    rw [hm]
    nlinarith
  let threshold := q / (2 * w * radiusDenominator)
  let coefficient := max (2 * expansionNumerator) (4 * expansionDenominator)
  let d := expansionNumerator * threshold / coefficient
  have hDivisorPositive : 0 < 2 * w * radiusDenominator := by positivity
  have hThresholdPositive : 0 < threshold := by
    exact Nat.div_pos hLiftLarge hDivisorPositive
  have hThresholdScale : 2 * w * threshold ≤ q := by
    calc
      2 * w * threshold ≤ (2 * w * threshold) * radiusDenominator := by
        exact Nat.le_mul_of_pos_right _ hRadiusDenominator
      _ = (2 * w * radiusDenominator) * threshold := by ring
      _ ≤ q := Nat.mul_div_le q (2 * w * radiusDenominator)
  have hForwardCaseOneRadius :
      radiusDenominator * (q * 1) ≤
        radiusNumerator *
          Fintype.card (Fin (w * n) × Cyclic.CyclicGroup q) := by
    simp [Fintype.card_prod, Cyclic.CyclicGroup, ZMod.card]
    have hbase : radiusDenominator ≤ radiusNumerator * (w * n) := by
      calc
        radiusDenominator ≤ n := hDenominatorLeN
        _ ≤ radiusNumerator * (w * n) := by
          simpa [Nat.mul_assoc] using
            (Nat.le_mul_of_pos_left n
              (Nat.mul_pos hRadiusNumerator hwPositive))
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_right q hbase
  have hTransposeCaseOneRadius :
      radiusDenominator * (q * 1) ≤
        radiusNumerator *
          Fintype.card (Fin m × Cyclic.CyclicGroup q) := by
    simp [Fintype.card_prod, Cyclic.CyclicGroup, ZMod.card]
    have hbase : radiusDenominator ≤ radiusNumerator * m := by
      exact hDenominatorLeM.trans
        (Nat.le_mul_of_pos_left m hRadiusNumerator)
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_right q hbase
  have hRadiusTimesThreshold : radiusDenominator * threshold ≤ q := by
    calc
      radiusDenominator * threshold ≤
          (2 * w) * (radiusDenominator * threshold) := by
        exact Nat.le_mul_of_pos_left _ (by positivity)
      _ = (2 * w * radiusDenominator) * threshold := by ring
      _ ≤ q := Nat.mul_div_le q (2 * w * radiusDenominator)
  have hForwardCaseTwoRadius :
      radiusDenominator * threshold ≤
        radiusNumerator *
          Fintype.card (Fin (w * n) × Cyclic.CyclicGroup q) := by
    simp [Fintype.card_prod, Cyclic.CyclicGroup, ZMod.card]
    calc
      radiusDenominator * threshold ≤ q := hRadiusTimesThreshold
      _ ≤ radiusNumerator * ((w * n) * q) := by
        simpa [Nat.mul_assoc] using
          (Nat.le_mul_of_pos_left q
            (Nat.mul_pos hRadiusNumerator (Nat.mul_pos hwPositive hnPositive)))
  have hTransposeCaseTwoRadius :
      radiusDenominator * threshold ≤
        radiusNumerator *
          Fintype.card (Fin m × Cyclic.CyclicGroup q) := by
    simp [Fintype.card_prod, Cyclic.CyclicGroup, ZMod.card]
    calc
      radiusDenominator * threshold ≤ q := hRadiusTimesThreshold
      _ ≤ radiusNumerator * (m * q) := by
        simpa [Nat.mul_assoc] using
          (Nat.le_mul_of_pos_left q
            (Nat.mul_pos hRadiusNumerator hmPositive))
  have hCoefficientPositive : 0 < coefficient := by
    exact lt_of_lt_of_le (by positivity) (Nat.le_max_left _ _)
  have hLower : coefficient * d ≤
      expansionNumerator * min (q * 1) threshold := by
    have hThresholdLeQ : threshold ≤ q :=
      (Nat.div_le_self q _)
    simp only [mul_one, Nat.min_eq_right hThresholdLeQ]
    exact Nat.mul_div_le _ _
  have hFinite := finite_distance_locality_of_relativeExpansion
    q hqTwo A 1 1 w threshold
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator d
    (by norm_num) (by norm_num) hExpansionNumerator hwPositive
      hThresholdPositive hThresholdScale hForwardWeight hTransposeWeight
      hForwardRelative hTransposeRelative hForwardCaseOneRadius
      hForwardCaseTwoRadius hTransposeCaseOneRadius
      hTransposeCaseTwoRadius hLower hLower
  have hDimension := finrank_middleHomology_bounds q hqOdd A
  unfold FirstFamilyMember
  dsimp only
  have hRowsLtColumns : m < w * n := by
    rw [hm]
    have hFactor : 2 * (w / 4) < w := by omega
    simpa [Nat.mul_assoc] using
      (Nat.mul_lt_mul_of_pos_right hFactor hnPositive)
  have hUpperRaw := middleCohomologyDistanceAtMost_lift A
    (Cyclic.cyclicGenerator q)
    (by simpa [Cyclic.CyclicGroup, ZMod.card] using hqOdd)
    (by simpa using hRowsLtColumns)
  have hUpper : MiddleCohomologyDistanceAtMost
      (LiftedProduct.chainComplex (Cyclic.data q A)) q := by
    simpa [Cyclic.data, Cyclic.CyclicGroup, ZMod.card] using hUpperRaw
  refine ⟨hqOdd, hm, hnLower, hnUpper, ?_, ?_, ?_, hFinite.1,
    hFinite.2.1, hFinite.2.2.1, hFinite.2.2.2, hUpper, ?_⟩
  · simpa [blockLength] using
      (Cyclic.card_qubitIndex (aRow := Fin m) (aCol := Fin (w * n)) q)
  · simpa using hDimension.1
  · simpa using hDimension.2
  · have hThresholdLeQ : threshold ≤ q := Nat.div_le_self q _
    simpa [certifiedDistanceLowerBound, threshold, coefficient, d,
      Nat.min_eq_right hThresholdLeQ] using hLower
end QEC.Coding.ExpanderCodes.PK20
