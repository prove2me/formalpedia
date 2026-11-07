-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.PKDistance.zero_horizontalClass_caseTwo_invGenerator_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:44:11.517872+00:00
-- url     : https://prove2.me/submissions/f577cb57-32f8-41ab-a004-39aef699fc34

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_horizontalPart_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_HammingWeight_eq_horizontalPart_add_verticalPart
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_cyclic_card_le_HammingWeight_caseTwoRemainder_invGenerator
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_verticalPart_lowerBound_of_caseTwo_invPrimitive_crossing
import Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_normalized_horizontalPrimitive_invGenerator_of_projection_eq_zero
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
import Theorems.Thm_QEC_Coding_HammingWeight_add_le
import Theorems.Thm_QEC_Coding_HammingWeight_linearMap_le_of_basis
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


attribute [local simp] QEC.Coding.BalancedProduct.PKDistance.horizontalPart_apply
attribute [local simp] QEC.Coding.BalancedProduct.PKDistance.verticalPart_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w
namespace QEC.Coding.BalancedProduct.PKDistance
theorem _root_.solution
    {aRow aCol : Type}
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    (q : Nat) [NeZero q] (hq : 2 ≤ q)
    (A : Matrix aRow aCol
      (MonoidAlgebra (ZMod 2) (Cyclic.CyclicGroup q)))
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol Unit Unit
        (Cyclic.CyclicGroup q)))
    (hz : z ∈ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleCycleCode.carrier)
    (hzNotBoundary : z ∉ (LiftedProduct.chainComplex
      (Cyclic.liftedProductData A
        (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryCode.carrier)
    (hProjected : HorizontalSubsystem.horizontalHomologyProjection A
      (Cyclic.cyclicGenerator q)⁻¹
      ((LiftedProduct.chainComplex
        (Cyclic.liftedProductData A
          (Cyclic.cyclicGenerator q)⁻¹)).middleBoundaryInCycles.mkQ
            ⟨z, hz⟩) = 0)
    (w threshold expansionRadius expansionNumerator expansionDenominator : Nat)
    (hw : 0 < w) (hthreshold : 0 < threshold)
    (hThresholdScale : 2 * w * threshold ≤ q)
    (hColumnWeight : ∀ i : aCol × Cyclic.CyclicGroup q,
      HammingWeight (tannerAction A (Pi.single i 1)) ≤ w)
    (hRadius : threshold ≤ expansionRadius)
    (hExpansion : (tannerAction A).SmallSetExpanding
      expansionRadius expansionNumerator expansionDenominator) :
    expansionNumerator * threshold ≤
      max (2 * expansionNumerator) (4 * expansionDenominator) *
        HammingWeight z := by
  let x := (Cyclic.cyclicGenerator q)⁻¹
  have hzBoundary : LiftedProduct.boundary1
      (Cyclic.liftedProductData A x) z = 0 :=
    ((LiftedProduct.chainComplex
      (Cyclic.liftedProductData A x)).mem_middleCycleCode_iff z).1 hz
  obtain ⟨h, hu, hhalf⟩ :=
    exists_normalized_horizontalPrimitive_invGenerator_of_projection_eq_zero
      q hq A z hz hProjected
  let horizontalWeight := HammingWeight (horizontalPart z)
  let verticalWeight := HammingWeight (verticalPart z)
  have hsplit : HammingWeight z = horizontalWeight + verticalWeight :=
    HammingWeight_eq_horizontalPart_add_verticalPart z
  have hhorizontal : horizontalWeight ≤ HammingWeight z := by omega
  have hvertical : verticalWeight ≤ HammingWeight z := by omega
  by_cases hHorizontalLarge : threshold ≤ 2 * horizontalWeight
  · calc
      expansionNumerator * threshold ≤
          expansionNumerator * (2 * horizontalWeight) :=
        Nat.mul_le_mul_left expansionNumerator hHorizontalLarge
      _ = (2 * expansionNumerator) * horizontalWeight := by ac_rfl
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          horizontalWeight :=
        Nat.mul_le_mul_right horizontalWeight (Nat.le_max_left _ _)
      _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
          HammingWeight z := Nat.mul_le_mul_left _ hhorizontal
  · by_cases hVerticalHalf : 2 * verticalWeight ≤ q
    · have hRemainder : q ≤ HammingWeight (caseTwoRemainder A z h) := by
        exact cyclic_card_le_HammingWeight_caseTwoRemainder_invGenerator
          q A z hzBoundary hzNotBoundary h hu
      have hTriangle : HammingWeight (caseTwoRemainder A z h) ≤
          HammingWeight (verticalPart z) + HammingWeight (tannerAction A h) :=
        HammingWeight_add_le (verticalPart z) (tannerAction A h)
      have hTanner : HammingWeight (tannerAction A h) ≤
          w * HammingWeight h :=
        HammingWeight_linearMap_le_of_basis
          (tannerAction A) w hColumnWeight h
      have hLower : q ≤ verticalWeight + w * HammingWeight h := by
        have := hRemainder.trans
          (hTriangle.trans (Nat.add_le_add_left hTanner _))
        simpa only [verticalWeight] using this
      have hPrimitiveScaled' : q ≤ 2 * (w * HammingWeight h) := by omega
      have hPrimitiveScaled : q ≤ 2 * w * HammingWeight h := by
        simpa only [Nat.mul_assoc] using hPrimitiveScaled'
      have hScaled : 2 * w * threshold ≤ 2 * w * HammingWeight h :=
        hThresholdScale.trans hPrimitiveScaled
      have hPrimitive : threshold ≤ HammingWeight h :=
        Nat.le_of_mul_le_mul_left hScaled (by omega)
      have hForced : expansionNumerator *
          (threshold - horizontalWeight) ≤
          2 * expansionDenominator * verticalWeight := by
        simpa only [horizontalWeight, verticalWeight] using
          verticalPart_lowerBound_of_caseTwo_invPrimitive_crossing
            q A z hzBoundary h hu hhalf threshold expansionRadius
              expansionNumerator expansionDenominator hthreshold hPrimitive
                hRadius hExpansion
      have hTwice : threshold ≤ 2 * (threshold - horizontalWeight) := by omega
      calc
        expansionNumerator * threshold ≤
            expansionNumerator * (2 * (threshold - horizontalWeight)) :=
          Nat.mul_le_mul_left expansionNumerator hTwice
        _ = 2 * (expansionNumerator *
            (threshold - horizontalWeight)) := by ac_rfl
        _ ≤ 2 * (2 * expansionDenominator * verticalWeight) :=
          Nat.mul_le_mul_left 2 hForced
        _ = (4 * expansionDenominator) * verticalWeight := by ring
        _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
            verticalWeight :=
          Nat.mul_le_mul_right verticalWeight (Nat.le_max_right _ _)
        _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
            HammingWeight z := Nat.mul_le_mul_left _ hvertical
    · have hThresholdLeQ : threshold ≤ q := by
        calc
          threshold = 1 * threshold := by rw [one_mul]
          _ ≤ (2 * w) * threshold :=
            Nat.mul_le_mul_right threshold (by omega)
          _ = 2 * w * threshold := by ac_rfl
          _ ≤ q := hThresholdScale
      have hThresholdVertical : threshold ≤ 2 * verticalWeight := by omega
      calc
        expansionNumerator * threshold ≤
            expansionNumerator * (2 * verticalWeight) :=
          Nat.mul_le_mul_left expansionNumerator hThresholdVertical
        _ = (2 * expansionNumerator) * verticalWeight := by ac_rfl
        _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
            verticalWeight :=
          Nat.mul_le_mul_right verticalWeight (Nat.le_max_left _ _)
        _ ≤ max (2 * expansionNumerator) (4 * expansionDenominator) *
            HammingWeight z := Nat.mul_le_mul_left _ hvertical
end QEC.Coding.BalancedProduct.PKDistance
