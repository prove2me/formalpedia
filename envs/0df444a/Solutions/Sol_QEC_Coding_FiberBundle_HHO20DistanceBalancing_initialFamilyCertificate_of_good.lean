-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HHO20DistanceBalancing.initialFamilyCertificate_of_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:40:31.380907+00:00
-- url     : https://prove2.me/submissions/b0b814ef-d1f9-47ce-ac60-f009b8c3b528

import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_DistanceBalancingLocality
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialLocality
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Asymptotics
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_initialXDistanceScaleAt_le_source
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_initialZDistanceScaleAt_le_source
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_initial_dimension_square_bounds
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_initial_x_distance_tradeoff
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_initial_z_distance_tradeoff
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_boundary_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_linearMapOfBasisImages_single
import Theorems.Thm_QEC_Coding_ClassicalWeightReduction_originalBoundary_single
import Theorems.Thm_QEC_Coding_DistanceBalancing_homologySliceMap_mk
import Theorems.Thm_QEC_Coding_DistanceBalancing_kernelTensorToSlices_tmul
import Theorems.Thm_QEC_Coding_FiberBundle_HHO20DistanceBalancing_balancedData_sourceChainComplex
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_baseSupportRelation_randomFiberBundleData_iff
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_bitNeighbor_incidenceRelation
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_checkNeighbor_incidenceRelation
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_distribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_groupedDistribution_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_independentProduct_apply
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_initialFiberBundle_boundedLocality
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
import Theorems.Thm_QEC_Coding_FiberBundle_card_hho20_qubitIndex
import Theorems.Thm_QEC_Coding_FiberBundle_cohomologyDistanceAtLeast_explicit
import Theorems.Thm_QEC_Coding_FiberBundle_finrank_middleHomology_eq_r
import Theorems.Thm_QEC_Coding_FiberBundle_homologyBaseProjection_add
import Theorems.Thm_QEC_Coding_FiberBundle_homologyDistanceAtLeast_explicit
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
theorem _root_.solution
    (s : Nat) (hs : 200 ≤ s)
    (baseSample : RandomBase.Sample (RandomPartition.hho20BaseScale s))
    (twistSample : RandomTwist.Sample
      (RandomPartition.hho20BaseScale s)
      (RandomPartition.hho20TypeCount s)
      (RandomPartition.hho20FiberLength s))
    [NeZero (RandomPartition.hho20TypeCount s)]
    [NeZero (RandomPartition.hho20FiberLength s)]
    [NeZero (RandomPartition.hho20FiberLength s - 1)]
    (hGood : RandomBase.IsFullyGood
      (Delta := RandomPartition.hho20DegreeScale s) baseSample)
    (hLTC : TwistGraph.HasHHO20LocalTestability
      (RandomPartition.hho20DegreeScale s) baseSample twistSample) :
    InitialFamilyCertificate s baseSample twistSample := by
  rcases hGood with ⟨⟨hDegree, hRank, hDistance⟩, hExpansion⟩
  let D₀ := RandomTwist.fiberBundleData baseSample twistSample
  let X₀ := chainComplex D₀
  let N₀ := Fintype.card
    (QubitIndex
      (Fin (3 * RandomPartition.hho20BaseScale s))
      (Fin (4 * RandomPartition.hho20BaseScale s))
      (ZMod (RandomPartition.hho20FiberLength s *
        RandomPartition.hho20FiberLength s))
      (ZMod (RandomPartition.hho20FiberLength s *
        RandomPartition.hho20FiberLength s)))
  let K₀ := Module.finrank (ZMod 2) X₀.middleHomology
  have hDelta : 1 ≤ RandomPartition.hho20DegreeScale s := by
    exact Nat.one_le_iff_ne_zero.mpr (by
      simp only [RandomPartition.hho20DegreeScale,
        RandomPartition.hho20TypeCount]
      positivity)
  have hXSource := cohomologyDistanceAtLeast_explicit
    baseSample twistSample hRank hDelta hDegree hExpansion
  have hXSource' : CohomologyDistanceAtLeast D₀
      (min (RandomPartition.hho20FiberLength s ^ 2 / 2)
        ((6 * RandomPartition.hho20BaseScale s) /
          (100000 * RandomPartition.hho20DegreeScale s))) := by
    intro z hz hnontrivial
    simpa only [ZMod.card, pow_two] using hXSource z hz hnontrivial
  have hZSource := homologyDistanceAtLeast_explicit
    baseSample twistSample hRank hDistance hLTC hDelta
  have hX : CohomologyDistanceAtLeast D₀
      (initialXDistanceScaleAt s) := by
    intro z hz hnontrivial
    exact (initialXDistanceScaleAt_le_source s hs).trans
      (hXSource' z hz hnontrivial)
  have hZ : HomologyDistanceAtLeast D₀
      (initialZDistanceScaleAt s) := by
    intro z hz hnontrivial
    exact (initialZDistanceScaleAt_le_source s hs).trans
      (hZSource z hz hnontrivial)
  have hLocality : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X₀).localityProfile
      (initialLocalityScaleAt s) := by
    exact RandomBase.initialFiberBundle_boundedLocality
      baseSample twistSample hDegree
  have hN : N₀ = initialBlocklengthAt s := by
    dsimp only [N₀, initialBlocklengthAt]
    rw [card_hho20_qubitIndex]
    ring
  have hK : K₀ = initialDimensionAt s := by
    dsimp only [K₀, X₀, D₀, initialDimensionAt]
    exact finrank_middleHomology_eq_r baseSample twistSample hRank
  have hSquare := initial_dimension_square_bounds s hs
  have hSquareOne : N₀ ≤ 7 * K₀ ^ 2 := by
    rw [hN, hK]
    exact hSquare.1
  have hSquareTwo : 7 * K₀ ^ 2 ≤ 2 * N₀ := by
    rw [hN, hK]
    exact hSquare.2
  have hXTradeoff := initial_x_distance_tradeoff s N₀
    (initialXDistanceScaleAt s) hs (by simpa [hN]) (le_refl _)
  have hZTradeoff := initial_z_distance_tradeoff s N₀
    (initialZDistanceScaleAt s) hs (by simpa [hN]) (le_refl _)
  unfold InitialFamilyCertificate
  dsimp only
  exact ⟨binaryCSSCode_stabilizer_isSourceValidBinary D₀,
    hX, hZ, hLocality, hN, hK,
    hSquareOne, hSquareTwo,
    hXTradeoff, hZTradeoff⟩
end QEC.Coding.FiberBundle.HHO20DistanceBalancing
