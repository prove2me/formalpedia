-- Prove2me | solution 1 for QEC.Locality.WeightedBoundaryEdgeRecursion.existsUnique_edgeOwner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:45:09.234395+00:00
-- url     : https://prove2.me/submissions/78a1b404-64eb-41dd-ba05-5d9751620365

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
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
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
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
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
attribute [local simp] QEC.Locality.MarkedSeparatorSpine.exposedSide_stop
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
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
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


section
namespace QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
private theorem weightedSpineEdges_exact_cover
    (edges : Finset (ι × ι)) (first second : Finset ι) :
    weightedSpineFirstEdges edges first ∪
        (weightedSpineSecondEdges edges first second ∪
          weightedSpineThirdEdges edges first second) = edges := by
  ext edge
  simp only [weightedSpineFirstEdges, weightedSpineSecondEdges, weightedSpineThirdEdges,
    Finset.mem_union, Finset.mem_filter]
  simp only [touches]
  tauto
private theorem weightedSpineEdges_pairwiseDisjoint
    (edges : Finset (ι × ι)) (first second : Finset ι) :
    Disjoint (weightedSpineFirstEdges edges first)
        (weightedSpineSecondEdges edges first second) ∧
      Disjoint (weightedSpineFirstEdges edges first)
        (weightedSpineThirdEdges edges first second) ∧
      Disjoint (weightedSpineSecondEdges edges first second)
        (weightedSpineThirdEdges edges first second) := by
  classical
  constructor
  · apply Finset.disjoint_left.mpr
    intro edge hfirst hsecond
    exact (Finset.mem_filter.mp hsecond).2.1 (Finset.mem_filter.mp hfirst).2
  constructor
  · apply Finset.disjoint_left.mpr
    intro edge hfirst hthird
    exact (Finset.mem_filter.mp hthird).2.1 (Finset.mem_filter.mp hfirst).2
  · apply Finset.disjoint_left.mpr
    intro edge hsecond hthird
    exact (Finset.mem_filter.mp hthird).2.2 (Finset.mem_filter.mp hsecond).2.2
end QEC.Locality
end

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace WeightedBoundaryEdgeRecursion
theorem _root_.solution
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary)
    (edge : ι × ι) (hedge : edge ∈ edges) :
    ∃! owner : tree.edgeOwnerType, edge ∈ tree.edgeRegion owner := by
  classical
  induction tree generalizing edge with
  | leaf _ _ _ _ _ _ =>
      refine ⟨Unit.unit, by simpa [edgeRegion] using hedge, ?_⟩
      intro owner _
      simpa [edgeOwnerType] using (Subsingleton.elim (α := Unit) owner Unit.unit)
  | @split edges vertices boundary hsubset hsymmetric hincident hboundary hcard spine
      hseparatorCard hboundaryLarge
      firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      let firstEdges := weightedSpineFirstEdges edges spine.exposedSide
      let secondEdges := weightedSpineSecondEdges edges spine.exposedSide spine.stopSides.1
      let thirdEdges := weightedSpineThirdEdges edges spine.exposedSide spine.stopSides.1
      by_cases hfirst : edge ∈ firstEdges
      · rcases ihFirst edge hfirst with ⟨owner, howner, hunique⟩
        refine ⟨Sum.inl owner, by simpa [edgeRegion] using howner, ?_⟩
        intro candidate hcandidate
        cases candidate with
        | inl candidate =>
            exact congrArg Sum.inl (hunique candidate (by simpa [edgeRegion] using hcandidate))
        | inr candidate =>
            cases candidate with
            | inl candidate =>
                have hsecond : edge ∈ secondEdges :=
                  secondTree.edgeRegion_subset candidate (by simpa [edgeRegion] using hcandidate)
                exact False.elim
                  ((Finset.disjoint_left.mp
                    (weightedSpineEdges_pairwiseDisjoint edges spine.exposedSide
                      spine.stopSides.1).1) hfirst hsecond)
            | inr candidate =>
                have hthird : edge ∈ thirdEdges :=
                  thirdTree.edgeRegion_subset candidate (by simpa [edgeRegion] using hcandidate)
                exact False.elim
                  ((Finset.disjoint_left.mp
                    (weightedSpineEdges_pairwiseDisjoint edges spine.exposedSide
                      spine.stopSides.1).2.1) hfirst hthird)
      · by_cases hsecond : edge ∈ secondEdges
        · rcases ihSecond edge hsecond with ⟨owner, howner, hunique⟩
          refine ⟨Sum.inr (Sum.inl owner), by simpa [edgeRegion] using howner, ?_⟩
          intro candidate hcandidate
          cases candidate with
          | inl candidate =>
              have hfirst' : edge ∈ firstEdges :=
                firstTree.edgeRegion_subset candidate (by simpa [edgeRegion] using hcandidate)
              exact False.elim (hfirst hfirst')
          | inr candidate =>
              cases candidate with
              | inl candidate =>
                  exact congrArg (fun x => Sum.inr (Sum.inl x))
                    (hunique candidate (by simpa [edgeRegion] using hcandidate))
              | inr candidate =>
                  have hthird : edge ∈ thirdEdges :=
                    thirdTree.edgeRegion_subset candidate (by simpa [edgeRegion] using hcandidate)
                  exact False.elim
                    ((Finset.disjoint_left.mp
                      (weightedSpineEdges_pairwiseDisjoint edges spine.exposedSide
                        spine.stopSides.1).2.2) hsecond hthird)
        · have hthird : edge ∈ thirdEdges := by
            have hcover := Finset.ext_iff.mp
              (weightedSpineEdges_exact_cover edges spine.exposedSide spine.stopSides.1) edge
            have : edge ∈ firstEdges ∪ (secondEdges ∪ thirdEdges) := hcover.mpr hedge
            rcases Finset.mem_union.mp this with hfirst' | hrest
            · exact False.elim (hfirst hfirst')
            · rcases Finset.mem_union.mp hrest with hsecond' | hthird'
              · exact False.elim (hsecond hsecond')
              · exact hthird'
          rcases ihThird edge hthird with ⟨owner, howner, hunique⟩
          refine ⟨Sum.inr (Sum.inr owner), by simpa [edgeRegion] using howner, ?_⟩
          intro candidate hcandidate
          cases candidate with
          | inl candidate =>
              have hfirst' : edge ∈ firstEdges :=
                firstTree.edgeRegion_subset candidate (by simpa [edgeRegion] using hcandidate)
              exact False.elim (hfirst hfirst')
          | inr candidate =>
              cases candidate with
              | inl candidate =>
                  have hsecond' : edge ∈ secondEdges :=
                    secondTree.edgeRegion_subset candidate (by simpa [edgeRegion] using hcandidate)
                  exact False.elim (hsecond hsecond')
              | inr candidate =>
                  exact congrArg (fun x => Sum.inr (Sum.inr x))
                    (hunique candidate (by simpa [edgeRegion] using hcandidate))
end WeightedBoundaryEdgeRecursion
end QEC.Locality
