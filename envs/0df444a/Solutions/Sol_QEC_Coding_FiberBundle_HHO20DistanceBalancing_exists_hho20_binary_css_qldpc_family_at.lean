-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HHO20DistanceBalancing.exists_hho20_binary_css_qldpc_family_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:57:29.655509+00:00
-- url     : https://prove2.me/submissions/1e4c66db-ff7d-4286-b313-d5c658127b5c

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
import Definitions.Def_QEC_Results_QLDPC_FiberBundleFamily
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_DistanceBalancing_homologySliceMap_mk
import Theorems.Thm_QEC_Coding_DistanceBalancing_kernelTensorToSlices_tmul
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_balancedBlocklengthUpperAt_le_scale
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_balancedData_sourceChainComplex
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_balancedLocalityComplex_bounded_eight
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_balancedLocalityComplex_eq
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_dimensionScale_le_baseScale_product
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_dimension_three_fifths
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_distanceScaleAt_le_cohomology
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_distanceScaleAt_le_homology
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_distance_three_fifths
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_exists_distanceBalancedCode_at
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_finrank_middleHomology_le_card
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_initialFamilyCertificate_of_good
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_baseSupportRelation_randomFiberBundleData_iff
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_bitNeighbor_incidenceRelation
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_checkNeighbor_incidenceRelation
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_baseSample_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_isTail_twistSample
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_typeTwist_twistSample
import Theorems.Thm_QEC_Coding_FiberBundle_RandomTwist_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_blockEquiv_apply
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_conj_stdAddChar_neg
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_eq_sub
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_inNeighbor_outNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badHeavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_badNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_heavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_lightLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_mediumLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_nonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_twoSidedLightTypeSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableHeavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_mem_usableNonheavyLayerSet_iff
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_eq_add
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_outNeighbor_inNeighbor
import Theorems.Thm_QEC_Coding_FiberBundle_binaryCSSCode_stabilizer_isSourceValidBinary
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_mem_horizontalBoundaryShadow_iff
import Theorems.Thm_QEC_Coding_FiberBundle_multipleRotation_val
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inl
import Theorems.Thm_QEC_Coding_FiberBundle_translateBundleWord_apply_inr
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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
attribute [local simp] QEC.Coding.ClassicalWeightReduction.boundary_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.linearMapOfBasisImages_single
attribute [local simp] QEC.Coding.ClassicalWeightReduction.originalBoundary_single
attribute [local simp] QEC.Coding.DistanceBalancing.homologySliceMap_mk
attribute [local simp] QEC.Coding.DistanceBalancing.kernelTensorToSlices_tmul
attribute [local simp] QEC.Coding.FiberBundle.HHO20DistanceBalancing.balancedData_sourceChainComplex
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.baseSupportRelation_randomFiberBundleData_iff
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.card_bitNeighbor_incidenceRelation
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.card_checkNeighbor_incidenceRelation
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.columnDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.groupedDistribution_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomBase.independentProduct_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.baseSample_apply
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.isTail_twistSample
attribute [local simp] QEC.Coding.FiberBundle.RandomPartition.typeTwist_twistSample
attribute [local simp] QEC.Coding.FiberBundle.RandomTwist.distribution_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.blockEquiv_apply
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.conj_stdAddChar_neg
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_eq_sub
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.inNeighbor_outNeighbor
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_badHeavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_badNonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_heavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_lightLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_mediumLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_nonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_twoSidedLightTypeSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_usableHeavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.mem_usableNonheavyLayerSet_iff
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_eq_add
attribute [local simp] QEC.Coding.FiberBundle.TwistGraph.outNeighbor_inNeighbor
attribute [local simp] QEC.Coding.FiberBundle.homologyBaseProjection_add
attribute [local simp] QEC.Coding.FiberBundle.mem_horizontalBoundaryShadow_iff
attribute [local simp] QEC.Coding.FiberBundle.multipleRotation_val
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inl
attribute [local simp] QEC.Coding.FiberBundle.translateBundleWord_apply_inr
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
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
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.HHO20DistanceBalancing
open QEC.Coding
universe u
namespace QEC.Coding.FiberBundle.HHO20DistanceBalancing
theorem _root_.solution :
    ∀ (s : Nat), ∀ (hs : 200 ≤ s),
    letI : NeZero (RandomPartition.hho20TypeCount (2 * s)) :=
      ⟨RandomPartition.hho20TypeCount_ne_zero (2 * s) (by omega)⟩
    letI : NeZero (RandomPartition.hho20FiberLength (2 * s)) :=
      ⟨by
        have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
        omega⟩
    letI : NeZero (RandomPartition.hho20FiberLength (2 * s) - 1) :=
      ⟨by
        have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
        omega⟩
    ∃ (baseSample : RandomBase.Sample
          (RandomPartition.hho20BaseScale (2 * s)))
        (twistSample : RandomTwist.Sample
          (RandomPartition.hho20BaseScale (2 * s))
          (RandomPartition.hho20TypeCount (2 * s))
          (RandomPartition.hho20FiberLength (2 * s)))
        (balanceSample : RandomBase.Sample
          (RandomPartition.hho20BaseScale s)),
      let X := finalComplex
        baseSample twistSample balanceSample
      let N := Fintype.card
        (FinalQubitIndex baseSample twistSample balanceSample)
      let K := Module.finrank (ZMod 2) X.middleHomology
      InitialFamilyCertificate (2 * s) baseSample twistSample ∧
        (X.binaryCSSCode).stabilizer.IsSourceValidBinary ∧
        MiddleHomologyDistanceAtLeast X (distanceScaleAt s) ∧
        MiddleCohomologyDistanceAtLeast X (distanceScaleAt s) ∧
        BoundedLocality
          (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile 8 ∧
        dimensionScaleAt s ≤ K ∧
        N ≤ blocklengthScaleAt s ∧
        RandomPartition.hho20FiberLength s ^ 6 ≤ N ∧
        N ^ 3 ≤ dimensionTradeoffCoefficient * s ^ 12 * K ^ 5 ∧
        N ^ 3 ≤ distanceTradeoffCoefficient * s ^ 32 *
          distanceScaleAt s ^ 5 := by
  intro s hs
  letI : NeZero (RandomPartition.hho20TypeCount (2 * s)) :=
    ⟨RandomPartition.hho20TypeCount_ne_zero (2 * s) (by omega)⟩
  letI : NeZero (RandomPartition.hho20FiberLength (2 * s)) :=
    ⟨by
      have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
      omega⟩
  letI : NeZero (RandomPartition.hho20FiberLength (2 * s) - 1) :=
    ⟨by
      have := RandomPartition.hho20_fiberLength_ge (2 * s) (by omega)
      omega⟩
  obtain ⟨baseSample, twistSample, balanceSample, hAll⟩ :=
    exists_distanceBalancedCode_at s hs
  have hDistances := hAll.1
  have hBlocklength := hAll.2.1
  have hDimension := hAll.2.2.1
  have hMainGood := hAll.2.2.2.1
  have hMainLTC := hAll.2.2.2.2.1
  have hInitial : InitialFamilyCertificate (2 * s)
      baseSample twistSample := by
    exact initialFamilyCertificate_of_good (2 * s) (by omega)
      baseSample twistSample hMainGood hMainLTC
  let X := finalComplex baseSample twistSample balanceSample
  let N := Fintype.card
    (FinalQubitIndex baseSample twistSample balanceSample)
  let K := Module.finrank (ZMod 2) X.middleHomology
  have hComplex : X = DistanceBalancing.chainComplex
      (balancedData baseSample twistSample balanceSample) := by
    change balancedLocalityComplex baseSample twistSample balanceSample = _
    exact balancedLocalityComplex_eq baseSample twistSample balanceSample
  have hHomology : MiddleHomologyDistanceAtLeast X
      (balancedHomologyDistanceAt s) := by
    rw [hComplex]
    exact hDistances.1
  have hCohomology : MiddleCohomologyDistanceAtLeast X
      (balancedCohomologyDistanceAt s) := by
    rw [hComplex]
    exact hDistances.2
  have hHomologyScale : MiddleHomologyDistanceAtLeast X
      (distanceScaleAt s) := by
    intro z hz hnontrivial
    exact (distanceScaleAt_le_homology s hs).trans
      (hHomology z hz hnontrivial)
  have hCohomologyScale : MiddleCohomologyDistanceAtLeast X
      (distanceScaleAt s) := by
    intro z hz hnontrivial
    exact (distanceScaleAt_le_cohomology s hs).trans
      (hCohomology z hz hnontrivial)
  have hLocality : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile 8 := by
    exact balancedLocalityComplex_bounded_eight
      baseSample twistSample balanceSample
  have hK : dimensionScaleAt s ≤ K := by
    dsimp only [K]
    rw [hComplex]
    exact (dimensionScale_le_baseScale_product s hs).trans hDimension
  have hN : N ≤ blocklengthScaleAt s := by
    change Fintype.card
        (DistanceBalancing.QubitIndex
          (MainQubit baseSample twistSample)
          (MainCZero baseSample twistSample)
          (BalanceBit balanceSample) (BalanceCheck balanceSample)) ≤
      blocklengthScaleAt s
    exact hBlocklength.trans (balancedBlocklengthUpperAt_le_scale s hs)
  have hKN : K ≤ N := by
    exact finrank_middleHomology_le_card X
  have hExponential : RandomPartition.hho20FiberLength s ^ 6 ≤ N := by
    apply (show RandomPartition.hho20FiberLength s ^ 6 ≤
        dimensionScaleAt s by rfl).trans
    exact hK.trans hKN
  have hKTradeoff := dimension_three_fifths s N K (by omega) hN hK
  have hDTradeoff := distance_three_fifths s N (distanceScaleAt s)
    hs hN (le_refl _)
  refine ⟨baseSample, twistSample, balanceSample, ?_⟩
  dsimp only
  exact ⟨hInitial, X.binaryCSSCode_stabilizer_isSourceValidBinary,
    hHomologyScale, hCohomologyScale, hLocality, hK, hN,
    hExponential, hKTradeoff, hDTradeoff⟩
end QEC.Coding.FiberBundle.HHO20DistanceBalancing
