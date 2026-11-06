-- Prove2me | solution 1 for QEC.Locality.exists_bgklCorrectablePartition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:16:05.706208+00:00
-- url     : https://prove2.me/submissions/20656de1-2865-4d35-b53b-babf51f0def4

import Definitions.Def_QEC_Locality_SeparatorProfile_ExplicitDivision
import Definitions.Def_QEC_Locality_CorrectablePartition_Core
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_ExplicitProfileEdgeDivision_isolated_not_mem_incident
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_bgklSmallBoundaryCorrectable
import Theorems.Thm_QEC_Locality_bgklSmallBoundaryEpsilon_pos
import Theorems.Thm_QEC_Locality_complement_interiors_subset_sharedBoundary_union_isolated
import Theorems.Thm_QEC_Locality_edgeDivisionInteriors_fixedGeneratorDecoupled
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled
import Theorems.Thm_QEC_Locality_exists_uniform_explicitProfileEdgeDivision
import Theorems.Thm_QEC_Locality_markedSpineDecayRatio_lt_one
import Theorems.Thm_QEC_Locality_mem_directedEdgeFinset_iff
import Theorems.Thm_QEC_Locality_mem_edgeDivisionSharedBoundary_iff
import Theorems.Thm_QEC_Locality_mem_edgeIncidentVertices_iff
import Theorems.Thm_QEC_Locality_mem_fixedGeneratorOuterBoundaryFinset_iff
import Theorems.Thm_QEC_Locality_mem_graphIsolatedVertices_iff
import Theorems.Thm_QEC_Locality_profileDivisionRegionConstant_pos
import Theorems.Thm_QEC_Locality_semanticStabilizerDistance_erasureRecoverableFromRegister
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
noncomputable section
namespace QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
private theorem mem_explicitDivisionPieceActive_inl_iff
    (G : ConnectivityGraph ι) {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap)
    (owner : division.Owner) :
    Sum.inl owner ∈ explicitDivisionPieceActive G division ↔ owner ∈ division.active := by
  classical
  simp [explicitDivisionPieceActive]
private theorem mem_explicitDivisionPieceActive_inr_iff
    (G : ConnectivityGraph ι) {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap)
    (vertex : ι) :
    Sum.inr vertex ∈ explicitDivisionPieceActive G division ↔
      vertex ∈ graphIsolatedVertices G := by
  classical
  simp [explicitDivisionPieceActive]
private theorem explicitDivisionCorrectableUnion_selected :
    ∀ (G : ConnectivityGraph ι) {incidentCap localBoundaryCap activeCountCap : Nat}
      (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap),
    (explicitDivisionCorrectableUnion G division).selected =
      (division.active.biUnion fun owner =>
        explicitDivisionInterior division owner) ∪
        graphIsolatedVertices G := by
  intro G incidentCap localBoundaryCap activeCountCap division
  classical
  ext vertex
  simp [explicitDivisionCorrectableUnion, familyUnionSubsystem,
    explicitDivisionPieceActive, explicitDivisionPiece, finiteSubsystemOfFinset]
private theorem explicitDivisionPieces_fixedGeneratorDecoupled
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision P.fixedGeneratorInteractionGraph
      incidentCap localBoundaryCap activeCountCap)
    {a b : division.Owner ⊕ ι}
    (ha : a ∈ explicitDivisionPieceActive P.fixedGeneratorInteractionGraph division)
    (hb : b ∈ explicitDivisionPieceActive P.fixedGeneratorInteractionGraph division)
    (hab : a ≠ b) :
    P.fixedGeneratorDecoupled
      ((explicitDivisionPiece P.fixedGeneratorInteractionGraph division a).selected : Set ι)
      ((explicitDivisionPiece P.fixedGeneratorInteractionGraph division b).selected : Set ι) := by
  classical
  letI := division.ownerDecidableEq
  rcases a with owner | vertex <;> rcases b with other | other
  · have howner := (mem_explicitDivisionPieceActive_inl_iff
      P.fixedGeneratorInteractionGraph division owner).1 ha
    have hother := (mem_explicitDivisionPieceActive_inl_iff
      P.fixedGeneratorInteractionGraph division other).1 hb
    have hne : owner ≠ other := by
      intro heq
      apply hab
      exact congrArg Sum.inl heq
    exact edgeDivisionInteriors_fixedGeneratorDecoupled P division.isEdgeDivision howner hother hne
  · have howner := (mem_explicitDivisionPieceActive_inl_iff
      P.fixedGeneratorInteractionGraph division owner).1 ha
    have hisolated := (mem_explicitDivisionPieceActive_inr_iff
      P.fixedGeneratorInteractionGraph division other).1 hb
    constructor
    · apply Set.disjoint_left.mpr
      intro x hxInterior hxSingleton
      have hxInterior' : x ∈ explicitDivisionInterior division owner := by
        simpa [explicitDivisionPiece, finiteSubsystemOfFinset] using hxInterior
      have hxSingleton' : x = other := by
        simpa [explicitDivisionPiece, finiteSubsystemOfFinset] using hxSingleton
      subst x
      apply division.isolated_not_mem_incident hisolated owner howner
      have hxRaw : other ∈ edgeDivisionInterior division.region division.active owner := by
        simpa only [explicitDivisionInterior] using hxInterior'
      exact (Finset.mem_sdiff.mp hxRaw).1
    · intro x hxInterior y hySingleton hxy
      have hySingleton' : y = other := by
        simpa [explicitDivisionPiece, finiteSubsystemOfFinset] using hySingleton
      subst y
      exact (mem_graphIsolatedVertices_iff P.fixedGeneratorInteractionGraph other).1 hisolated x
        (P.fixedGeneratorInteractionGraph.symmetric hxy)
  · have hisolated := (mem_explicitDivisionPieceActive_inr_iff
      P.fixedGeneratorInteractionGraph division vertex).1 ha
    have hother := (mem_explicitDivisionPieceActive_inl_iff
      P.fixedGeneratorInteractionGraph division other).1 hb
    constructor
    · apply Set.disjoint_left.mpr
      intro x hxSingleton hxInterior
      have hxSingleton' : x = vertex := by
        simpa [explicitDivisionPiece, finiteSubsystemOfFinset] using hxSingleton
      have hxInterior' : x ∈ explicitDivisionInterior division other := by
        simpa [explicitDivisionPiece, finiteSubsystemOfFinset] using hxInterior
      subst x
      apply division.isolated_not_mem_incident hisolated other hother
      have hxRaw : vertex ∈ edgeDivisionInterior division.region division.active other := by
        simpa only [explicitDivisionInterior] using hxInterior'
      exact (Finset.mem_sdiff.mp hxRaw).1
    · intro x hxSingleton y hyInterior hxy
      have hxSingleton' : x = vertex := by
        simpa [explicitDivisionPiece, finiteSubsystemOfFinset] using hxSingleton
      subst x
      exact (mem_graphIsolatedVertices_iff P.fixedGeneratorInteractionGraph vertex).1 hisolated y hxy
  · have hvertex := (mem_explicitDivisionPieceActive_inr_iff
      P.fixedGeneratorInteractionGraph division vertex).1 ha
    have hother := (mem_explicitDivisionPieceActive_inr_iff
      P.fixedGeneratorInteractionGraph division other).1 hb
    have hne : vertex ≠ other := by
      intro heq
      apply hab
      exact congrArg Sum.inr heq
    constructor
    · apply Set.disjoint_left.mpr
      intro x hxVertex hxOther
      have hxVertex' : x = vertex := by
        simpa [explicitDivisionPiece, finiteSubsystemOfFinset] using hxVertex
      have hxOther' : x = other := by
        simpa [explicitDivisionPiece, finiteSubsystemOfFinset] using hxOther
      exact hne (hxVertex'.symm.trans hxOther')
    · intro x hxVertex y hyOther hxy
      have hxVertex' : x = vertex := by
        simpa [explicitDivisionPiece, finiteSubsystemOfFinset] using hxVertex
      subst x
      exact (mem_graphIsolatedVertices_iff P.fixedGeneratorInteractionGraph vertex).1 hvertex y hxy
private theorem exists_erasureRecovery_of_explicitDivisionPieces
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d) (hdn : d ≤ Fintype.card ι) (hdTwo : 1 < d)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (beta exponent : ℝ)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hexponent : exponent < 1)
    {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision P.fixedGeneratorInteractionGraph
      incidentCap localBoundaryCap activeCountCap)
    (hSmall : ∀ owner, owner ∈ division.active →
      ((explicitDivisionInterior division owner).card : ℝ) ≤
        Real.rpow (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹)
    (hBoundary : ∀ owner, owner ∈ division.active →
      4 * (fixedGeneratorOuterBoundaryFinset P
        (explicitDivisionInterior division owner)).card ≤ d) :
    ∃ recovery : QuantumChannel
        (explicitDivisionCorrectableUnion P.fixedGeneratorInteractionGraph division).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (explicitDivisionCorrectableUnion P.fixedGeneratorInteractionGraph division).complementSystem
        P.semanticCode
        ((explicitDivisionCorrectableUnion P.fixedGeneratorInteractionGraph division).erasureChannelFromRegister) recovery := by
  classical
  letI := division.ownerDecidableEq
  apply exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled P
  · intro piece hpiece
    rcases piece with owner | vertex
    · have howner := (mem_explicitDivisionPieceActive_inl_iff
        P.fixedGeneratorInteractionGraph division owner).1 hpiece
      exact bgklSmallBoundaryCorrectable P d hd hdn hDistance beta exponent hProfile hexponent
          (edgeDivisionInterior division.region division.active owner)
          (by simpa [explicitDivisionInterior] using hSmall owner howner)
          (by simpa [explicitDivisionInterior] using hBoundary owner howner)
    · have hSelected : (finiteSubsystemOfFinset ({vertex} : Finset ι)).selected.card < d := by
        simpa [finiteSubsystemOfFinset] using hdTwo
      exact semanticStabilizerDistance_erasureRecoverableFromRegister
          P.code d hDistance (finiteSubsystemOfFinset ({vertex} : Finset ι)) hSelected
  · intro a ha b hb hab
    exact explicitDivisionPieces_fixedGeneratorDecoupled P division ha hb hab
private theorem complement_explicitDivisionCorrectableUnion_subset_sharedBoundary
    (G : ConnectivityGraph ι) {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap) :
    Finset.univ \ (explicitDivisionCorrectableUnion G division).selected ⊆
      explicitDivisionSharedBoundary division := by
  classical
  letI := division.ownerDecidableEq
  rw [explicitDivisionCorrectableUnion_selected]
  intro vertex hvertex
  have hnotUnion := (Finset.mem_sdiff.mp hvertex).2
  have hnotInterior : vertex ∉
      division.active.biUnion (fun owner => explicitDivisionInterior division owner) := by
    intro hinterior
    exact hnotUnion (Finset.mem_union_left _ hinterior)
  have hrawComplement : vertex ∈ Finset.univ \
      division.active.biUnion (fun owner =>
        edgeDivisionInterior division.region division.active owner) := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa only [explicitDivisionInterior] using hnotInterior
  have hcover := complement_interiors_subset_sharedBoundary_union_isolated division.isEdgeDivision
    hrawComplement
  rcases Finset.mem_union.mp hcover with hshared | hisolated
  · simpa only [explicitDivisionSharedBoundary] using hshared
  · exact (hnotUnion (Finset.mem_union_right _ hisolated)).elim
private theorem sharedBoundary_subset_active_localBoundaries
    (G : ConnectivityGraph ι) {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap) :
    explicitDivisionSharedBoundary division ⊆
      division.active.biUnion (explicitDivisionLocalBoundary division) := by
  classical
  letI := division.ownerDecidableEq
  change edgeDivisionSharedBoundary division.region division.active ⊆
    division.active.biUnion (fun owner =>
      edgeIncidentVertices (division.region owner) ∩
        edgeDivisionSharedBoundary division.region division.active)
  intro vertex hvertex
  rcases (mem_edgeDivisionSharedBoundary_iff division.region division.active vertex).1 hvertex with
    ⟨owner, howner, _other, _hother, _hne, hincident, _⟩
  exact Finset.mem_biUnion.mpr ⟨owner, howner, Finset.mem_inter.mpr ⟨hincident, hvertex⟩⟩
private theorem sharedBoundary_card_le_active_mul_localBoundaryCap
    (G : ConnectivityGraph ι) {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap) :
    (explicitDivisionSharedBoundary division).card ≤
      division.active.card * localBoundaryCap := by
  classical
  letI := division.ownerDecidableEq
  change (edgeDivisionSharedBoundary division.region division.active).card ≤
    division.active.card * localBoundaryCap
  exact (Finset.card_le_card (by
    exact sharedBoundary_subset_active_localBoundaries G division)).trans
    (Finset.card_biUnion_le_card_mul division.active
      (fun owner => edgeIncidentVertices (division.region owner) ∩
        edgeDivisionSharedBoundary division.region division.active)
      localBoundaryCap division.localBoundary_card_le)
private theorem explicitDivisionCorrectableUnion_complement_card_le
    (G : ConnectivityGraph ι) {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap) :
    (Finset.univ \ (explicitDivisionCorrectableUnion G division).selected).card ≤
      division.active.card * localBoundaryCap :=
  (Finset.card_le_card
    (complement_explicitDivisionCorrectableUnion_subset_sharedBoundary G division)).trans
      (sharedBoundary_card_le_active_mul_localBoundaryCap G division)
omit [Fintype ι] in
private theorem endpoint_mem_explicitDivisionRegion
    {m : Type v} [DecidableEq m] (regions : m → Finset (ι × ι))
    {owner : m} {source target : ι} (hedge : (source, target) ∈ regions owner) :
    source ∈ edgeIncidentVertices (regions owner) ∧
      target ∈ edgeIncidentVertices (regions owner) := by
  constructor
  · exact (mem_edgeIncidentVertices_iff (regions owner) source).2
      ⟨(source, target), hedge, Or.inl rfl⟩
  · exact (mem_edgeIncidentVertices_iff (regions owner) target).2
      ⟨(source, target), hedge, Or.inr rfl⟩
private theorem explicitDivisionInterior_incident_owner_unique
    {m : Type v} [DecidableEq m] (regions : m → Finset (ι × ι)) (active : Finset m)
    {owner candidate : m} (howner : owner ∈ active) (hcandidate : candidate ∈ active)
    {vertex : ι} (hinterior : vertex ∈ edgeDivisionInterior regions active owner)
    (hincident : vertex ∈ edgeIncidentVertices (regions candidate)) : candidate = owner := by
  classical
  by_contra hne
  have hinterior' := Finset.mem_sdiff.mp hinterior
  exact hinterior'.2 ((mem_edgeDivisionSharedBoundary_iff regions active vertex).2
    ⟨owner, howner, candidate, hcandidate, Ne.symm hne, hinterior'.1, hincident⟩)
private theorem fixedGeneratorOuterBoundary_explicitDivisionInterior_subset_localBoundary
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision P.fixedGeneratorInteractionGraph
      incidentCap localBoundaryCap activeCountCap)
    {owner : division.Owner} (howner : owner ∈ division.active) :
    fixedGeneratorOuterBoundaryFinset P (explicitDivisionInterior division owner) ⊆
      explicitDivisionLocalBoundary division owner := by
  classical
  letI := division.ownerDecidableEq
  change fixedGeneratorOuterBoundaryFinset P
      (edgeDivisionInterior division.region division.active owner) ⊆
    edgeIncidentVertices (division.region owner) ∩
      edgeDivisionSharedBoundary division.region division.active
  intro vertex hvertex
  rw [mem_fixedGeneratorOuterBoundaryFinset_iff] at hvertex
  rcases hvertex with ⟨hvertexInterior, source, hsourceInterior, hsourceVertex⟩
  have hedge : (source, vertex) ∈ directedEdgeFinset P.fixedGeneratorInteractionGraph :=
    (mem_directedEdgeFinset_iff _ source vertex).2 hsourceVertex
  rcases division.isEdgeDivision.2.2 (source, vertex) hedge with
    ⟨edgeOwner, ⟨hedgeOwner, hedgeRegion⟩, _⟩
  have hendpoints := endpoint_mem_explicitDivisionRegion division.region hedgeRegion
  have hOwnerEq := explicitDivisionInterior_incident_owner_unique division.region division.active howner
    hedgeOwner hsourceInterior hendpoints.1
  subst edgeOwner
  have hvertexShared : vertex ∈ edgeDivisionSharedBoundary division.region division.active := by
    by_contra hnotShared
    apply hvertexInterior
    exact Finset.mem_sdiff.mpr ⟨hendpoints.2, hnotShared⟩
  exact Finset.mem_inter.mpr ⟨hendpoints.2, hvertexShared⟩
private theorem fixedGeneratorOuterBoundary_explicitDivisionInterior_card_le
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision P.fixedGeneratorInteractionGraph
      incidentCap localBoundaryCap activeCountCap)
    {owner : division.Owner} (howner : owner ∈ division.active) :
    (fixedGeneratorOuterBoundaryFinset P (explicitDivisionInterior division owner)).card ≤
      localBoundaryCap :=
  (Finset.card_le_card
    (fixedGeneratorOuterBoundary_explicitDivisionInterior_subset_localBoundary P division howner)).trans
      (by
        exact division.localBoundary_card_le owner howner)
private theorem explicitDivisionInterior_card_le_incidentCap
    {G : ConnectivityGraph ι} {incidentCap localBoundaryCap activeCountCap : Nat}
    (division : ExplicitProfileEdgeDivision G incidentCap localBoundaryCap activeCountCap)
    {owner : division.Owner} (howner : owner ∈ division.active) :
    (explicitDivisionInterior division owner).card ≤ incidentCap := by
  classical
  letI := division.ownerDecidableEq
  calc
    (explicitDivisionInterior division owner).card ≤
        (edgeIncidentVertices (division.region owner)).card := by
      apply Finset.card_le_card
      exact (Finset.sdiff_subset : edgeIncidentVertices (division.region owner) \
          edgeDivisionSharedBoundary division.region division.active ⊆
          edgeIncidentVertices (division.region owner))
    _ ≤ incidentCap := division.incident_card_le owner howner
private theorem bgklPartitionBoundaryCoefficient_pos
    {beta exponent : ℝ} (hbeta : 1 ≤ beta) (hexponent : 0 < exponent) :
    0 < bgklPartitionBoundaryCoefficient beta exponent := by
  unfold bgklPartitionBoundaryCoefficient
  exact div_pos (zero_lt_one.trans_le hbeta)
    (sub_pos.mpr (markedSpineDecayRatio_lt_one hexponent))
private theorem bgklPartitionEpsilon_pos
    {beta exponent : ℝ} (hbeta : 1 ≤ beta) (hexponent : 0 < exponent) :
    0 < bgklPartitionEpsilon beta exponent := by
  unfold bgklPartitionEpsilon
  exact lt_min (bgklSmallBoundaryEpsilon_pos hbeta hexponent)
    (one_div_pos.mpr (mul_pos (by norm_num) (bgklPartitionBoundaryCoefficient_pos hbeta hexponent)))
private theorem bgklPartitionEpsilon_le_smallBoundaryEpsilon
    (beta exponent : ℝ) :
    bgklPartitionEpsilon beta exponent ≤ bgklSmallBoundaryEpsilon beta exponent := by
  exact min_le_left _ _
private theorem bgklPartitionEpsilon_le_boundaryInverse
    (beta exponent : ℝ) :
    bgklPartitionEpsilon beta exponent ≤
      1 / (96 * bgklPartitionBoundaryCoefficient beta exponent) := by
  exact min_le_right _ _
private theorem bgklPartitionScaleTarget_pos
    {beta exponent : ℝ} (hbeta : 1 ≤ beta) (hexponent : 0 < exponent)
    {d : Nat} (hd : 0 < d) :
    0 < bgklPartitionScaleTarget beta exponent d := by
  unfold bgklPartitionScaleTarget
  exact Real.rpow_pos_of_pos
    (mul_pos (bgklPartitionEpsilon_pos hbeta hexponent) (by exact_mod_cast hd)) _
private theorem bgklPartitionScale_le_target
    {beta exponent : ℝ} (hbeta : 1 ≤ beta) (hexponent : 0 < exponent)
    {d : Nat} (hd : 0 < d) :
    ((bgklPartitionScale beta exponent d : Nat) : ℝ) ≤
      bgklPartitionScaleTarget beta exponent d := by
  unfold bgklPartitionScale
  exact Nat.floor_le (bgklPartitionScaleTarget_pos hbeta hexponent hd).le
private theorem bgklPartitionScaleTarget_rpow_eq
    {beta exponent : ℝ} (hbeta : 1 ≤ beta) (hexponent : 0 < exponent)
    {d : Nat} (hd : 0 < d) :
    Real.rpow (bgklPartitionScaleTarget beta exponent d) exponent =
      bgklPartitionEpsilon beta exponent * d := by
  unfold bgklPartitionScaleTarget
  exact Real.rpow_inv_rpow
    (mul_nonneg (bgklPartitionEpsilon_pos hbeta hexponent).le
      (by exact_mod_cast hd.le))
    (ne_of_gt hexponent)
private theorem bgklPartitionScale_rpow_le
    {beta exponent : ℝ} (hbeta : 1 ≤ beta) (hexponent : 0 < exponent)
    {d : Nat} (hd : 0 < d) :
    Real.rpow (bgklPartitionScale beta exponent d) exponent ≤
      bgklPartitionEpsilon beta exponent * d := by
  calc
    Real.rpow (bgklPartitionScale beta exponent d) exponent ≤
        Real.rpow (bgklPartitionScaleTarget beta exponent d) exponent :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (bgklPartitionScale_le_target hbeta hexponent hd)
        hexponent.le
    _ = bgklPartitionEpsilon beta exponent * d :=
      bgklPartitionScaleTarget_rpow_eq hbeta hexponent hd
private theorem distance_le_ninetySix_mul_div_fortyEight {d : Nat} (hd : 96 ≤ d) :
    d ≤ 96 * (d / 48) := by
  have hquotient : 1 ≤ d / 48 := by omega
  have hmod : d % 48 < 48 := Nat.mod_lt _ (by omega)
  have hdecomposition : d % 48 + 48 * (d / 48) = d := Nat.mod_add_div _ _
  omega
private theorem weightedProfileBoundaryBudget_le_distance_eighth
    {beta exponent : ℝ} (hbeta : 1 ≤ beta) (hexponent : 0 < exponent)
    {d : Nat} (hd : 96 ≤ d) :
    weightedProfileBoundaryBudget beta exponent (bgklPartitionScale beta exponent d) ≤ d / 8 := by
  let boundaryCoefficient := bgklPartitionBoundaryCoefficient beta exponent
  have hboundaryCoefficient : 0 < boundaryCoefficient :=
    bgklPartitionBoundaryCoefficient_pos hbeta hexponent
  have hproduct : boundaryCoefficient * bgklPartitionEpsilon beta exponent ≤ 1 / 96 := by
    calc
      boundaryCoefficient * bgklPartitionEpsilon beta exponent ≤
          boundaryCoefficient * (1 / (96 * boundaryCoefficient)) := by
        gcongr
        exact bgklPartitionEpsilon_le_boundaryInverse beta exponent
      _ = 1 / 96 := by
        field_simp [hboundaryCoefficient.ne']
  have hbudgetReal : boundaryCoefficient *
      Real.rpow (bgklPartitionScale beta exponent d) exponent ≤ (d : ℝ) / 96 := by
    calc
      boundaryCoefficient * Real.rpow (bgklPartitionScale beta exponent d) exponent ≤
          boundaryCoefficient * (bgklPartitionEpsilon beta exponent * d) := by
        gcongr
        exact bgklPartitionScale_rpow_le hbeta hexponent (by omega)
      _ = (boundaryCoefficient * bgklPartitionEpsilon beta exponent) * d := by ring
      _ ≤ (1 / 96 : ℝ) * d := by gcongr
      _ = (d : ℝ) / 96 := by ring
  have hdiv : (d : ℝ) / 96 ≤ (d / 48 : Nat) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 96)).2
    exact_mod_cast (by
      simpa [mul_comm] using (distance_le_ninetySix_mul_div_fortyEight hd))
  have hceil : Nat.ceil (boundaryCoefficient *
      Real.rpow (bgklPartitionScale beta exponent d) exponent) ≤ d / 48 :=
    Nat.ceil_le.mpr (hbudgetReal.trans hdiv)
  rw [weightedProfileBoundaryBudget, weightedSpineSeparatorBudget,
    show beta / (1 - markedSpineDecayRatio exponent) = boundaryCoefficient by rfl]
  calc
    6 * Nat.ceil (boundaryCoefficient * Real.rpow (bgklPartitionScale beta exponent d) exponent) ≤
        6 * (d / 48) := Nat.mul_le_mul_left _ hceil
    _ = ((d / 8) / 6) * 6 := by
      rw [Nat.div_div_eq_div_mul]
      ring
    _ ≤ d / 8 := Nat.div_mul_le_self _ _
private theorem distance_div_partitionScaleTarget
    {epsilon exponent d : ℝ} (hepsilon : 0 < epsilon) (hexponent : 0 < exponent)
    (hd : 0 < d) :
    d / Real.rpow (epsilon * d) exponent⁻¹ =
      Real.rpow epsilon (-exponent⁻¹) /
        Real.rpow d ((1 - exponent) / exponent) := by
  have hepsilonNonneg : 0 ≤ epsilon := hepsilon.le
  have hdNonneg : 0 ≤ d := hd.le
  have hepsilonPowPos : 0 < Real.rpow epsilon exponent⁻¹ :=
    Real.rpow_pos_of_pos hepsilon _
  have dPowPos : 0 < Real.rpow d exponent⁻¹ := Real.rpow_pos_of_pos hd _
  have hexponentNe : exponent ≠ 0 := ne_of_gt hexponent
  have hExponent : exponent⁻¹ - 1 = (1 - exponent) / exponent := by
    field_simp
  calc
    d / Real.rpow (epsilon * d) exponent⁻¹ =
        d / (Real.rpow epsilon exponent⁻¹ * Real.rpow d exponent⁻¹) := by
      congr 1
      exact Real.mul_rpow hepsilonNonneg hdNonneg
    _ = (Real.rpow epsilon exponent⁻¹)⁻¹ *
        (d / Real.rpow d exponent⁻¹) := by
      field_simp
    _ = Real.rpow epsilon (-exponent⁻¹) *
        (d / Real.rpow d exponent⁻¹) := by
      have hneg : Real.rpow epsilon (-exponent⁻¹) =
          (Real.rpow epsilon exponent⁻¹)⁻¹ :=
        Real.rpow_neg hepsilonNonneg exponent⁻¹
      rw [hneg]
    _ = Real.rpow epsilon (-exponent⁻¹) /
        (Real.rpow d exponent⁻¹ / d) := by
      field_simp
    _ = Real.rpow epsilon (-exponent⁻¹) /
        Real.rpow d (exponent⁻¹ - 1) := by
      have hsub : Real.rpow d (exponent⁻¹ - 1) =
          Real.rpow d exponent⁻¹ / d :=
        Real.rpow_sub_one hd.ne' exponent⁻¹
      rw [hsub]
    _ = Real.rpow epsilon (-exponent⁻¹) /
        Real.rpow d ((1 - exponent) / exponent) := by rw [hExponent]
private theorem fixedGeneratorOuterBoundaryFinset_univ_eq_empty
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ)) :
    fixedGeneratorOuterBoundaryFinset P Finset.univ = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro vertex hvertex
  rw [mem_fixedGeneratorOuterBoundaryFinset_iff] at hvertex
  exact hvertex.1 (by simp)
private theorem exists_erasureRecovery_of_empty
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d) :
    ∃ recovery : QuantumChannel (finiteSubsystemOfFinset (∅ : Finset ι)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (finiteSubsystemOfFinset (∅ : Finset ι)).complementSystem
        P.semanticCode (finiteSubsystemOfFinset (∅ : Finset ι)).erasureChannelFromRegister recovery := by
  exact semanticStabilizerDistance_erasureRecoverableFromRegister
    P.code d hDistance (finiteSubsystemOfFinset (∅ : Finset ι))
      (by simpa [finiteSubsystemOfFinset] using hd)
private theorem exists_erasureRecovery_of_univ
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (d : Nat) (hd : 0 < d) (hdn : d ≤ Fintype.card ι)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (beta exponent : ℝ)
    (hProfile : P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent)
    (hexponent : exponent < 1)
    (hSmall : (Fintype.card ι : ℝ) ≤ bgklPartitionScaleTarget beta exponent d) :
    ∃ recovery : QuantumChannel (finiteSubsystemOfFinset (Finset.univ : Finset ι)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (finiteSubsystemOfFinset (Finset.univ : Finset ι)).complementSystem P.semanticCode
        (finiteSubsystemOfFinset (Finset.univ : Finset ι)).erasureChannelFromRegister recovery := by
  have hSmallBoundary : (Fintype.card ι : ℝ) ≤
      Real.rpow (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹ := by
    calc
      (Fintype.card ι : ℝ) ≤ bgklPartitionScaleTarget beta exponent d := hSmall
      _ = Real.rpow (bgklPartitionEpsilon beta exponent * d) exponent⁻¹ := rfl
      _ ≤ Real.rpow (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹ := by
        apply Real.rpow_le_rpow
        · exact mul_nonneg (bgklPartitionEpsilon_pos hProfile.1 hProfile.2.1).le
            (by exact_mod_cast hd.le)
        · gcongr
          exact bgklPartitionEpsilon_le_smallBoundaryEpsilon beta exponent
        · exact inv_nonneg.mpr hProfile.2.1.le
  apply bgklSmallBoundaryCorrectable P d hd hdn hDistance beta exponent hProfile hexponent
  · simpa [finiteSubsystemOfFinset] using hSmallBoundary
  · simp [fixedGeneratorOuterBoundaryFinset_univ_eq_empty]
private theorem bgklPartitionSmallCutoff_pos
    {beta exponent : ℝ} :
    0 < bgklPartitionSmallCutoff beta exponent := by
  unfold bgklPartitionSmallCutoff
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
private theorem bgklPartitionAlpha_pos
    {beta exponent : ℝ} (hbeta : 1 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1) :
    0 < bgklPartitionAlpha beta exponent := by
  have hcoefficient : 0 < profileDivisionRegionConstant beta exponent :=
    profileDivisionRegionConstant_pos hbeta hexponent
  have htail : 0 ≤ (profileDivisionRegionConstant beta exponent + 1) *
      Real.rpow (bgklPartitionEpsilon beta exponent) (-exponent⁻¹) := by
    apply mul_nonneg
    · linarith
    · exact Real.rpow_nonneg (bgklPartitionEpsilon_pos hbeta hexponent.1).le _
  have hcutoff : 0 ≤ Real.rpow (bgklPartitionSmallCutoff beta exponent)
      ((1 - exponent) / exponent) :=
    Real.rpow_nonneg
      (bgklPartitionSmallCutoff_pos (beta := beta) (exponent := exponent)).le _
  unfold bgklPartitionAlpha
  linarith
private theorem distance_lt_bgklPartitionSmallCutoff_of_not_large
    {beta exponent : ℝ} (hbeta : 1 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1)
    {d : Nat} (hd : 0 < d)
    (hnotLarge : ¬ (96 ≤ d ∧ 2 ≤ bgklPartitionScale beta exponent d ∧
      profileDivisionThreshold beta exponent ≤ bgklPartitionScale beta exponent d)) :
    (d : ℝ) < bgklPartitionSmallCutoff beta exponent := by
  by_cases hdLarge : 96 ≤ d
  · have hscaleSmall : bgklPartitionScale beta exponent d <
        max 2 (profileDivisionThreshold beta exponent) := by
      omega
    have hfloorSmall : Nat.floor (bgklPartitionScaleTarget beta exponent d) <
        max 2 (profileDivisionThreshold beta exponent) := by
      simpa [bgklPartitionScale] using hscaleSmall
    have htargetSmall : bgklPartitionScaleTarget beta exponent d <
        (max 2 (profileDivisionThreshold beta exponent) : ℝ) := by
      refine (Nat.lt_floor_add_one _).trans_le ?_
      exact_mod_cast Nat.succ_le_of_lt hfloorSmall
    have hpower : bgklPartitionEpsilon beta exponent * d <
        Real.rpow (max 2 (profileDivisionThreshold beta exponent)) exponent := by
      calc
        bgklPartitionEpsilon beta exponent * d =
            Real.rpow (bgklPartitionScaleTarget beta exponent d) exponent :=
          (bgklPartitionScaleTarget_rpow_eq hbeta hexponent.1 hd).symm
        _ < Real.rpow (max 2 (profileDivisionThreshold beta exponent)) exponent :=
          Real.rpow_lt_rpow (bgklPartitionScaleTarget_pos hbeta hexponent.1 hd).le
            htargetSmall hexponent.1
    have hratio : (d : ℝ) < Real.rpow (max 2 (profileDivisionThreshold beta exponent)) exponent /
        bgklPartitionEpsilon beta exponent := by
      apply (lt_div_iff₀ (bgklPartitionEpsilon_pos hbeta hexponent.1)).2
      simpa [mul_comm] using hpower
    exact hratio.trans_le (le_max_right _ _)
  · exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_of_not_ge hdLarge) (le_max_left _ _)
end QEC.Locality
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (beta exponent : ℝ) (hbeta : 1 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
        {κ : Type v} [Fintype κ]
        (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
        (d : Nat), 0 < d → d ≤ Fintype.card ι →
        StabilizerCode.SemanticStabilizerDistance P.code d →
        P.AssumedFixedGeneratorBGKLMeasuredProfilePowerUpperBound beta exponent →
        ∃ A : Finset ι, ∃ recovery : QuantumChannel (finiteSubsystemOfFinset A).complementSystem
            (Qubit.QubitRegister ι),
          Correctable (Qubit.QubitRegister ι) (finiteSubsystemOfFinset A).complementSystem
            P.semanticCode (finiteSubsystemOfFinset A).erasureChannelFromRegister recovery ∧
          ((Finset.univ \ A).card : ℝ) ≤ alpha * Fintype.card ι /
            Real.rpow d ((1 - exponent) / exponent) := by
  refine ⟨bgklPartitionAlpha beta exponent, bgklPartitionAlpha_pos hbeta hexponent, ?_⟩
  intro ι instFintype instDecidableEq κ instFintypeK P d hd hdn hDistance hProfile
  classical
  let target := bgklPartitionScaleTarget beta exponent d
  let scale := bgklPartitionScale beta exponent d
  let power := (1 - exponent) / exponent
  have hPowerPos : 0 < power := div_pos (sub_pos.mpr hexponent.2) hexponent.1
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hTargetPos : 0 < target := by
    simpa [target] using bgklPartitionScaleTarget_pos hbeta hexponent.1 hd
  have hPowerRpowPos : 0 < Real.rpow (d : ℝ) power :=
    Real.rpow_pos_of_pos hdReal _
  have hnRealPos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hd.trans_le hdn
  by_cases hTargetLarge : (Fintype.card ι : ℝ) ≤ target
  · rcases exists_erasureRecovery_of_univ P d hd hdn hDistance beta exponent hProfile hexponent.2
      (by simpa [target] using hTargetLarge) with ⟨recovery, hRecovery⟩
    refine ⟨Finset.univ, recovery, ?_, ?_⟩
    · simpa [finiteSubsystemOfFinset] using hRecovery
    · simp
      exact div_nonneg
        (mul_nonneg (bgklPartitionAlpha_pos hbeta hexponent).le hnRealPos.le)
        hPowerRpowPos.le
  have hTargetSmall : target < (Fintype.card ι : ℝ) := lt_of_not_ge hTargetLarge
  by_cases hLarge : 96 ≤ d ∧ 2 ≤ scale ∧ profileDivisionThreshold beta exponent ≤ scale
  · rcases exists_uniform_explicitProfileEdgeDivision beta exponent hbeta hexponent with
      ⟨threshold, countConstant, hthreshold, hcountConstant, _, hUpstream⟩
    subst threshold
    subst countConstant
    let division := Classical.choice (hUpstream P.fixedGeneratorInteractionGraph hProfile scale
      hLarge.2.1 hLarge.2.2)
    have hScaleLeTarget : (scale : ℝ) ≤ target := by
      simpa [scale, target] using bgklPartitionScale_le_target hbeta hexponent.1 hd
    have hScalePositive : 0 < (scale : ℝ) := by exact_mod_cast lt_of_lt_of_le (by omega) hLarge.2.1
    have hSmallInterior : ∀ owner, owner ∈ division.active →
        ((explicitDivisionInterior division owner).card : ℝ) ≤
          Real.rpow (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹ := by
      intro owner howner
      calc
        ((explicitDivisionInterior division owner).card : ℝ) ≤ (scale : ℝ) := by
          exact_mod_cast explicitDivisionInterior_card_le_incidentCap division howner
        _ ≤ target := hScaleLeTarget
        _ = Real.rpow (bgklPartitionEpsilon beta exponent * d) exponent⁻¹ := rfl
        _ ≤ Real.rpow (bgklSmallBoundaryEpsilon beta exponent * d) exponent⁻¹ := by
          apply Real.rpow_le_rpow
          · exact mul_nonneg (bgklPartitionEpsilon_pos hbeta hexponent.1).le hdReal.le
          · gcongr
            exact bgklPartitionEpsilon_le_smallBoundaryEpsilon beta exponent
          · exact inv_nonneg.mpr hexponent.1.le
    have hBoundaryInterior : ∀ owner, owner ∈ division.active →
        4 * (fixedGeneratorOuterBoundaryFinset P (explicitDivisionInterior division owner)).card ≤ d := by
      intro owner howner
      have hlocal := fixedGeneratorOuterBoundary_explicitDivisionInterior_card_le P division howner
      have hbudget : weightedProfileBoundaryBudget beta exponent scale ≤ d / 8 := by
        simpa [scale] using weightedProfileBoundaryBudget_le_distance_eighth hbeta hexponent.1 hLarge.1
      calc
        4 * (fixedGeneratorOuterBoundaryFinset P (explicitDivisionInterior division owner)).card ≤
            4 * weightedProfileBoundaryBudget beta exponent scale :=
          Nat.mul_le_mul_left _ hlocal
        _ ≤ 4 * (d / 8) := Nat.mul_le_mul_left _ hbudget
        _ ≤ 8 * (d / 8) := by omega
        _ = (d / 8) * 8 := by ring
        _ ≤ d := Nat.div_mul_le_self _ _
    rcases exists_erasureRecovery_of_explicitDivisionPieces P d hd hdn (by omega) hDistance
      beta exponent hProfile hexponent.2 division hSmallInterior hBoundaryInterior with
      ⟨recovery, hRecovery⟩
    let A := (explicitDivisionCorrectableUnion P.fixedGeneratorInteractionGraph division).selected
    refine ⟨A, recovery, ?_, ?_⟩
    · exact hRecovery
    · have hComplementNat := explicitDivisionCorrectableUnion_complement_card_le
        P.fixedGeneratorInteractionGraph division
      have hBudgetNat : weightedProfileBoundaryBudget beta exponent scale ≤ d / 8 := by
        simpa [scale] using
          weightedProfileBoundaryBudget_le_distance_eighth hbeta hexponent.1 hLarge.1
      have hComplementReal :
          ((Finset.univ \ A).card : ℝ) ≤ (division.active.card : ℝ) *
            weightedProfileBoundaryBudget beta exponent scale := by
        simpa [A] using (show
          ((Finset.univ \ (explicitDivisionCorrectableUnion P.fixedGeneratorInteractionGraph division).selected).card : ℝ) ≤
            (division.active.card : ℝ) * weightedProfileBoundaryBudget beta exponent scale by
          exact_mod_cast hComplementNat)
      have hBudgetReal : (weightedProfileBoundaryBudget beta exponent scale : ℝ) ≤ (d : ℝ) / 8 := by
        calc
          (weightedProfileBoundaryBudget beta exponent scale : ℝ) ≤ (d / 8 : Nat) := by
            exact_mod_cast hBudgetNat
          _ ≤ (d : ℝ) / 8 := Nat.cast_div_le
      have hCeilingInputNonneg : 0 ≤
          profileDivisionRegionConstant beta exponent * Fintype.card ι / scale := by
        positivity
      have hActiveReal : (division.active.card : ℝ) ≤
          profileDivisionRegionConstant beta exponent * Fintype.card ι / scale + 1 := by
        calc
          (division.active.card : ℝ) ≤
              (Nat.ceil (profileDivisionRegionConstant beta exponent * Fintype.card ι / scale) : ℝ) := by
            exact_mod_cast division.active_card_le
          _ ≤ profileDivisionRegionConstant beta exponent * Fintype.card ι / scale + 1 :=
            (Nat.ceil_lt_add_one hCeilingInputNonneg).le
      have hScaleFloor : target < (scale : ℝ) + 1 := by
        simpa [scale, bgklPartitionScale] using Nat.lt_floor_add_one target
      have hScaleAtLeastTwo : (2 : ℝ) ≤ scale := by exact_mod_cast hLarge.2.1
      have hTargetLeEightScale : target ≤ 8 * (scale : ℝ) := by nlinarith
      have hVertexScaleRatio : (Fintype.card ι : ℝ) / scale ≤
          8 * Fintype.card ι / target := by
        apply (div_le_div_iff₀ hScalePositive hTargetPos).2
        calc
          (Fintype.card ι : ℝ) * target ≤
              (Fintype.card ι : ℝ) * (8 * scale) :=
            mul_le_mul_of_nonneg_left hTargetLeEightScale (Nat.cast_nonneg _)
          _ = (8 * Fintype.card ι : ℝ) * scale := by ring
      have hInteriorTerm :
          (profileDivisionRegionConstant beta exponent * Fintype.card ι / scale) * ((d : ℝ) / 8) ≤
            profileDivisionRegionConstant beta exponent * ((d : ℝ) * Fintype.card ι / target) := by
        calc
          (profileDivisionRegionConstant beta exponent * Fintype.card ι / scale) * ((d : ℝ) / 8) =
              profileDivisionRegionConstant beta exponent *
                ((Fintype.card ι : ℝ) / scale) * ((d : ℝ) / 8) := by ring
          _ ≤ profileDivisionRegionConstant beta exponent *
              (8 * Fintype.card ι / target) * ((d : ℝ) / 8) := by gcongr
          _ = profileDivisionRegionConstant beta exponent *
              ((d : ℝ) * Fintype.card ι / target) := by
            field_simp [hTargetPos.ne']
      have hSingletonTerm : (d : ℝ) / 8 ≤ (d : ℝ) * Fintype.card ι / target := by
        calc
          (d : ℝ) / 8 ≤ d := by linarith
          _ ≤ (d : ℝ) * Fintype.card ι / target := by
            apply (le_div_iff₀ hTargetPos).2
            exact mul_le_mul_of_nonneg_left hTargetSmall.le hdReal.le
      have hCoefficientNonneg : 0 ≤
          (profileDivisionRegionConstant beta exponent + 1) *
            Real.rpow (bgklPartitionEpsilon beta exponent) (-exponent⁻¹) := by
        apply mul_nonneg
        · linarith [profileDivisionRegionConstant_pos hbeta hexponent]
        · exact Real.rpow_nonneg (bgklPartitionEpsilon_pos hbeta hexponent.1).le _
      have hAlphaCoefficient :
          (profileDivisionRegionConstant beta exponent + 1) *
              Real.rpow (bgklPartitionEpsilon beta exponent) (-exponent⁻¹) ≤
            bgklPartitionAlpha beta exponent := by
        unfold bgklPartitionAlpha
        have hcutoffNonneg := Real.rpow_nonneg
          (bgklPartitionSmallCutoff_pos (beta := beta) (exponent := exponent)).le
            ((1 - exponent) / exponent)
        have hprefix : 0 ≤ 1 +
            Real.rpow (bgklPartitionSmallCutoff beta exponent) ((1 - exponent) / exponent) := by
          exact add_nonneg (by norm_num) hcutoffNonneg
        linarith only [hprefix]
      calc
        ((Finset.univ \ A).card : ℝ) ≤
            (division.active.card : ℝ) * weightedProfileBoundaryBudget beta exponent scale := hComplementReal
        _ ≤ (profileDivisionRegionConstant beta exponent * Fintype.card ι / scale + 1) * ((d : ℝ) / 8) := by
          gcongr
        _ = (profileDivisionRegionConstant beta exponent * Fintype.card ι / scale) * ((d : ℝ) / 8) +
            (d : ℝ) / 8 := by ring
        _ ≤ profileDivisionRegionConstant beta exponent * ((d : ℝ) * Fintype.card ι / target) +
            (d : ℝ) * Fintype.card ι / target := add_le_add hInteriorTerm hSingletonTerm
        _ = (profileDivisionRegionConstant beta exponent + 1) *
            ((d : ℝ) * Fintype.card ι / target) := by ring
        _ = (profileDivisionRegionConstant beta exponent + 1) * Fintype.card ι *
            ((d : ℝ) / target) := by ring
        _ = (profileDivisionRegionConstant beta exponent + 1) * Fintype.card ι *
            (Real.rpow (bgklPartitionEpsilon beta exponent) (-exponent⁻¹) /
              Real.rpow d power) := by
          exact congrArg
            (fun ratio : ℝ => (profileDivisionRegionConstant beta exponent + 1) *
              Fintype.card ι * ratio)
            (distance_div_partitionScaleTarget
              (bgklPartitionEpsilon_pos hbeta hexponent.1) hexponent.1 hdReal)
        _ = ((profileDivisionRegionConstant beta exponent + 1) *
            Real.rpow (bgklPartitionEpsilon beta exponent) (-exponent⁻¹)) *
              Fintype.card ι / Real.rpow d power := by ring
        _ ≤ bgklPartitionAlpha beta exponent * Fintype.card ι /
            Real.rpow d power := by gcongr
  · rcases exists_erasureRecovery_of_empty P d hd hDistance with ⟨recovery, hRecovery⟩
    refine ⟨∅, recovery, ?_, ?_⟩
    · simpa [finiteSubsystemOfFinset] using hRecovery
    · have hDistanceCutoff : (d : ℝ) < bgklPartitionSmallCutoff beta exponent := by
        simpa [scale] using distance_lt_bgklPartitionSmallCutoff_of_not_large
          hbeta hexponent hd (by simpa [scale] using hLarge)
      have hCutoffPower : Real.rpow (d : ℝ) power ≤
          Real.rpow (bgklPartitionSmallCutoff beta exponent) power := by
        apply Real.rpow_le_rpow
        · exact Nat.cast_nonneg _
        · exact hDistanceCutoff.le
        · exact hPowerPos.le
      have hCoefficientNonneg : 0 ≤
          (profileDivisionRegionConstant beta exponent + 1) *
            Real.rpow (bgklPartitionEpsilon beta exponent) (-exponent⁻¹) := by
        apply mul_nonneg
        · linarith [profileDivisionRegionConstant_pos hbeta hexponent]
        · exact Real.rpow_nonneg (bgklPartitionEpsilon_pos hbeta hexponent.1).le _
      have hAlphaCutoff : Real.rpow (bgklPartitionSmallCutoff beta exponent) power ≤
          bgklPartitionAlpha beta exponent := by
        unfold bgklPartitionAlpha
        have hprefix : 0 ≤ 1 + Real.rpow (bgklPartitionSmallCutoff beta exponent)
            ((1 - exponent) / exponent) := by
          exact add_nonneg (by norm_num) (Real.rpow_nonneg
            (bgklPartitionSmallCutoff_pos (beta := beta) (exponent := exponent)).le _)
        calc
          Real.rpow (bgklPartitionSmallCutoff beta exponent) power ≤
              1 + Real.rpow (bgklPartitionSmallCutoff beta exponent) power := by linarith
          _ ≤ 1 + Real.rpow (bgklPartitionSmallCutoff beta exponent) power +
              (profileDivisionRegionConstant beta exponent + 1) *
                Real.rpow (bgklPartitionEpsilon beta exponent) (-exponent⁻¹) :=
            le_add_of_nonneg_right hCoefficientNonneg
      have hPowerAlpha : Real.rpow (d : ℝ) power ≤ bgklPartitionAlpha beta exponent :=
        hCutoffPower.trans hAlphaCutoff
      have hBound : (Fintype.card ι : ℝ) ≤
          bgklPartitionAlpha beta exponent * Fintype.card ι /
            Real.rpow d power := by
        apply (le_div_iff₀ hPowerRpowPos).2
        calc
          (Fintype.card ι : ℝ) * Real.rpow d power =
              Real.rpow d power * Fintype.card ι := by ring
          _ ≤ bgklPartitionAlpha beta exponent * Fintype.card ι :=
            mul_le_mul_of_nonneg_right hPowerAlpha (Nat.cast_nonneg _)
      simpa [power] using hBound
end QEC.Locality
