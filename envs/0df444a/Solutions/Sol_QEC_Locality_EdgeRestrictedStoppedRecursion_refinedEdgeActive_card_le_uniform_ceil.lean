-- Prove2me | solution 1 for QEC.Locality.EdgeRestrictedStoppedRecursion.refinedEdgeActive_card_le_uniform_ceil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:51:07.06367+00:00
-- url     : https://prove2.me/submissions/ab8d707a-dbdb-448b-9aa0-a5d7f1230294

import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
import Definitions.Def_QEC_Locality_SeparatorProfile_Completion
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedPotential
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_AssumedBGKLMeasuredProfilePowerUpperBound_edgeRestricted
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Locality_EdgeRestrictedStoppedRecursion_refinedEdgeActive_card_mul_budget_le
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Locality_WeightedBoundaryEdgeRecursion_edgeRegion_subset
import Theorems.Thm_QEC_Locality_edgeIncidentVertices_mono
import Theorems.Thm_QEC_Locality_markedSpineDecayRatio_lt_one
import Theorems.Thm_QEC_Locality_minimumSeparator_card_real_le_profilePower
import Theorems.Thm_QEC_Locality_profileDivisionPotentialCoefficient_nonneg
import Theorems.Thm_QEC_Locality_profileDivisionPotential_le_linear
import Theorems.Thm_QEC_Locality_profileDivisionPotential_le_root
import Theorems.Thm_QEC_Locality_profileDivisionPotential_linearScale_le_one_of_threshold
import Theorems.Thm_QEC_Locality_profileDivisionPotential_nonneg
import Theorems.Thm_QEC_Locality_profileDivisionPotential_split
import Theorems.Thm_QEC_Locality_separatorLeftEdges_incident_subset
import Theorems.Thm_QEC_Locality_separatorRightEdges_incident_subset
import Theorems.Thm_QEC_Locality_weightedSpineSeparatorBudget_pos
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
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
private theorem profileSplit_left_disjoint_separator
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting
      (edgeRestrictedGraph G edges) vertices left separator right) :
    Disjoint left separator := by
  apply Finset.disjoint_left.mpr
  intro x hxLeft hxSeparator
  have hxDiff : x ∈ vertices \ separator := by
    rw [← hpartition.2.1]
    exact Finset.mem_union_left _ hxLeft
  exact (Finset.mem_sdiff.mp hxDiff).2 hxSeparator
private theorem profileSplit_right_disjoint_separator
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting
      (edgeRestrictedGraph G edges) vertices left separator right) :
    Disjoint right separator := by
  apply Finset.disjoint_left.mpr
  intro x hxRight hxSeparator
  have hxDiff : x ∈ vertices \ separator := by
    rw [← hpartition.2.1]
    exact Finset.mem_union_right _ hxRight
  exact (Finset.mem_sdiff.mp hxDiff).2 hxSeparator
private theorem profileSplit_child_carrier_card_sum
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting
      (edgeRestrictedGraph G edges) vertices left separator right) :
    (left ∪ separator).card + (right ∪ separator).card =
      vertices.card + separator.card := by
  have hleftSeparator := profileSplit_left_disjoint_separator hpartition
  have hrightSeparator := profileSplit_right_disjoint_separator hpartition
  have hleftRight : Disjoint left right := hpartition.2.2.1
  have hseparatorRemainder : Disjoint separator (vertices \ separator) := by
    exact Finset.disjoint_left.mpr fun _ hs hr => (Finset.mem_sdiff.mp hr).2 hs
  have hseparatorCard : separator.card + (left ∪ right).card = vertices.card := by
    calc
      separator.card + (left ∪ right).card =
          separator.card + (vertices \ separator).card := by rw [← hpartition.2.1]
      _ = (separator ∪ (vertices \ separator)).card :=
        (Finset.card_union_of_disjoint hseparatorRemainder).symm
      _ = vertices.card := by rw [Finset.union_sdiff_of_subset hpartition.1]
  rw [Finset.card_union_of_disjoint hleftRight] at hseparatorCard
  rw [Finset.card_union_of_disjoint hleftSeparator,
    Finset.card_union_of_disjoint hrightSeparator]
  omega
private theorem profileSplit_left_carrier_interval
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting
      (edgeRestrictedGraph G edges) vertices left separator right) :
    vertices.card + separator.card ≤ 4 * (left ∪ separator).card ∧
      4 * (left ∪ separator).card ≤ 3 * (vertices.card + separator.card) := by
  have hleftSeparator := profileSplit_left_disjoint_separator hpartition
  have hrightSeparator := profileSplit_right_disjoint_separator hpartition
  have hleftRight : Disjoint left right := hpartition.2.2.1
  have hseparatorRemainder : Disjoint separator (vertices \ separator) := by
    exact Finset.disjoint_left.mpr fun _ hs hr => (Finset.mem_sdiff.mp hr).2 hs
  have hcard : separator.card + left.card + right.card = vertices.card := by
    calc
      separator.card + left.card + right.card =
          separator.card + (left ∪ right).card := by
        rw [Finset.card_union_of_disjoint hleftRight, Nat.add_assoc]
      _ = separator.card + (vertices \ separator).card := by rw [← hpartition.2.1]
      _ = (separator ∪ (vertices \ separator)).card :=
        (Finset.card_union_of_disjoint hseparatorRemainder).symm
      _ = vertices.card := by rw [Finset.union_sdiff_of_subset hpartition.1]
  rw [Finset.card_union_of_disjoint hleftSeparator]
  have hleftBalanced := hpartition.2.2.2.1
  have hrightBalanced := hpartition.2.2.2.2.1
  constructor <;> omega
private theorem profileSplit_right_carrier_interval
    {G : ConnectivityGraph ι} {edges : Finset (ι × ι)}
    {vertices left separator right : Finset ι}
    (hpartition : TwoThirdsBalancedPartitionAfterDeleting
      (edgeRestrictedGraph G edges) vertices left separator right) :
    vertices.card + separator.card ≤ 4 * (right ∪ separator).card ∧
      4 * (right ∪ separator).card ≤ 3 * (vertices.card + separator.card) := by
  have hsum := profileSplit_child_carrier_card_sum hpartition
  have hleft := profileSplit_left_carrier_interval hpartition
  omega
private theorem EdgeRestrictedStoppedRecursion.potential_amortizes_separatorCharge
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hstopped : tree.StoppedAtScale)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r)
    (hthreshold : profileDivisionThreshold beta exponent ≤ r)
    (hlower : r ≤ 4 * vertices.card) :
    (3 * tree.separatorCharge : Nat) + tree.terminalPotentialMass beta exponent ≤
      profileDivisionPotential beta exponent r vertices.card := by
  induction tree with
  | leaf hsubset hsymmetric hincident hcard =>
      simp [separatorCharge, terminalPotentialMass]
  | @split edges vertices left separator right hsubset hsymmetric hincident hpartition
      hminimum hleft hright leftTree rightTree ihLeft ihRight =>
      rcases hstopped with ⟨hlarge, hleftStopped, hrightStopped⟩
      have hsum := profileSplit_child_carrier_card_sum hpartition
      have hleftInterval := profileSplit_left_carrier_interval hpartition
      have hrightInterval := profileSplit_right_carrier_interval hpartition
      have hleftLower : r ≤ 4 * (left ∪ separator).card := by omega
      have hrightLower : r ≤ 4 * (right ∪ separator).card := by omega
      have hleftBound := ihLeft hleftStopped hleftLower
      have hrightBound := ihRight hrightStopped hrightLower
      have hvertices : 1 ≤ vertices.card := by omega
      have hseparatorReal : (separator.card : ℝ) ≤
          beta * (vertices.card : ℝ) ^ exponent :=
        minimumSeparator_card_real_le_profilePower
          (edgeRestrictedGraph G edges) beta exponent
          (hProfile.edgeRestricted G beta exponent edges) vertices separator
          hvertices hminimum
      have hscale := profileDivisionPotential_linearScale_le_one_of_threshold
        hProfile.1 hexponent hthreshold
      have hsplit := profileDivisionPotential_split
        (beta := beta) (exponent := exponent) (r := r)
        (parent := vertices.card) (left := (left ∪ separator).card)
        (right := (right ∪ separator).card) (separator := separator.card)
        (zero_le_one.trans hProfile.1) hexponent hr (by omega) hsum
        hleftInterval.1 hleftInterval.2 hseparatorReal hscale
      simp only [separatorCharge, terminalPotentialMass]
      push_cast at hleftBound hrightBound ⊢
      nlinarith
private theorem EdgeRestrictedStoppedRecursion.terminalPotentialMass_nonneg
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hstopped : tree.StoppedAtScale)
    (beta exponent : ℝ) (hbeta : 0 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r) (hlower : r ≤ 4 * vertices.card) :
    0 ≤ tree.terminalPotentialMass beta exponent := by
  induction tree with
  | leaf _ _ _ _ =>
      simpa [terminalPotentialMass] using
        profileDivisionPotential_nonneg hbeta hexponent hr hlower
  | @split _ vertices left separator right _ _ _ hpartition _ _ _
      leftTree rightTree ihLeft ihRight =>
      rcases hstopped with ⟨hlarge, hleftStopped, hrightStopped⟩
      have hleftInterval := profileSplit_left_carrier_interval hpartition
      have hrightInterval := profileSplit_right_carrier_interval hpartition
      have hleftLower : r ≤ 4 * (left ∪ separator).card := by omega
      have hrightLower : r ≤ 4 * (right ∪ separator).card := by omega
      exact add_nonneg (ihLeft hleftStopped hleftLower) (ihRight hrightStopped hrightLower)
private theorem EdgeRestrictedStoppedRecursion.separatorCharge_le_potential
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hstopped : tree.StoppedAtScale)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r)
    (hthreshold : profileDivisionThreshold beta exponent ≤ r)
    (hlower : r ≤ 4 * vertices.card) :
    (3 * tree.separatorCharge : Nat) ≤
      profileDivisionPotential beta exponent r vertices.card := by
  have hfull := tree.potential_amortizes_separatorCharge hstopped beta exponent
    hProfile hexponent hr hthreshold hlower
  have hterminal := tree.terminalPotentialMass_nonneg hstopped beta exponent
    (zero_le_one.trans hProfile.1) hexponent hr hlower
  norm_cast at hfull ⊢
  linarith
private theorem EdgeRestrictedStoppedRecursion.terminalCarrierMass_le_root_add_charge
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) :
    tree.terminalCarrierMass ≤ vertices.card + tree.separatorCharge := by
  induction tree with
  | leaf _ _ _ _ => simp [terminalCarrierMass, separatorCharge]
  | @split _ vertices left separator right _ _ _ hpartition _ _ _
      leftTree rightTree ihLeft ihRight =>
      have hsum := profileSplit_child_carrier_card_sum hpartition
      simp only [terminalCarrierMass, separatorCharge]
      omega
private theorem EdgeRestrictedStoppedRecursion.terminalOwnerCount_mul_scale_le_four_carrierMass
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hstopped : tree.StoppedAtScale) (hlower : r ≤ 4 * vertices.card) :
    tree.terminalOwnerCount * r ≤ 4 * tree.terminalCarrierMass := by
  induction tree with
  | leaf _ _ _ _ => simpa [terminalOwnerCount, terminalCarrierMass] using hlower
  | @split _ vertices left separator right _ _ _ hpartition _ _ _
      leftTree rightTree ihLeft ihRight =>
      rcases hstopped with ⟨hlarge, hleftStopped, hrightStopped⟩
      have hleftInterval := profileSplit_left_carrier_interval hpartition
      have hrightInterval := profileSplit_right_carrier_interval hpartition
      have hleftLower : r ≤ 4 * (left ∪ separator).card := by omega
      have hrightLower : r ≤ 4 * (right ∪ separator).card := by omega
      have hl := ihLeft hleftStopped hleftLower
      have hr := ihRight hrightStopped hrightLower
      simp only [terminalOwnerCount, terminalCarrierMass]
      rw [Nat.add_mul, Nat.mul_add]
      omega
omit [Fintype ι] in
private theorem separator_subset_leftRefinedBoundary
    (boundary left separator : Finset ι) :
    separator ⊆ leftRefinedBoundary boundary left separator :=
  Finset.subset_union_left
omit [Fintype ι] in
private theorem separator_subset_rightRefinedBoundary
    (boundary right separator : Finset ι) :
    separator ⊆ rightRefinedBoundary boundary right separator :=
  Finset.subset_union_left
omit [Fintype ι] in
/-- One separator split increases total propagated boundary by at most three copies. -/
private theorem profileSplit_child_boundary_card_sum_le
    (boundary left separator right : Finset ι) (hleftRight : Disjoint left right) :
    (leftRefinedBoundary boundary left separator).card +
        (rightRefinedBoundary boundary right separator).card ≤
      boundary.card + 3 * separator.card := by
  let leftPart := boundary ∩ (left ∪ separator)
  let rightPart := boundary ∩ (right ∪ separator)
  have hinter : leftPart ∩ rightPart ⊆ boundary ∩ separator := by
    intro x hx
    have hxLeft := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2
    have hxRight := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).2
    have hxBoundary := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
    rcases Finset.mem_union.mp hxLeft with hxLeft | hxSeparator
    · rcases Finset.mem_union.mp hxRight with hxRight | hxSeparator
      · exact False.elim ((Finset.disjoint_left.mp hleftRight) hxLeft hxRight)
      · exact Finset.mem_inter.mpr ⟨hxBoundary, hxSeparator⟩
    · exact Finset.mem_inter.mpr ⟨hxBoundary, hxSeparator⟩
  have hunion : leftPart ∪ rightPart ⊆ boundary :=
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hintersection :
      (boundary ∩ (left ∪ separator)).card +
          (boundary ∩ (right ∪ separator)).card ≤
        boundary.card + separator.card := by
    calc
      _ = (leftPart ∪ rightPart).card + (leftPart ∩ rightPart).card := by
        dsimp [leftPart, rightPart]
        exact (Finset.card_union_add_card_inter _ _).symm
      _ ≤ boundary.card + (boundary ∩ separator).card :=
        Nat.add_le_add (Finset.card_le_card hunion) (Finset.card_le_card hinter)
      _ ≤ boundary.card + separator.card :=
        Nat.add_le_add_left (Finset.card_le_card Finset.inter_subset_right) _
  simp only [leftRefinedBoundary, rightRefinedBoundary]
  have hleft := Finset.card_union_le separator (boundary ∩ (left ∪ separator))
  have hright := Finset.card_union_le separator (boundary ∩ (right ∪ separator))
  omega
private theorem EdgeRestrictedStoppedRecursion.propagatedBoundaryMass_le
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) (boundary : Finset ι) :
    tree.propagatedBoundaryMass boundary ≤ boundary.card + 3 * tree.separatorCharge := by
  induction tree generalizing boundary with
  | leaf _ _ _ _ =>
      exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp [separatorCharge])
  | @split _ _ left separator right _ _ _ hpartition _ _ _
      leftTree rightTree ihLeft ihRight =>
      have hchildren := profileSplit_child_boundary_card_sum_le boundary left separator right
        hpartition.2.2.1
      have hl := ihLeft (leftRefinedBoundary boundary left separator)
      have hr := ihRight (rightRefinedBoundary boundary right separator)
      simp only [propagatedBoundaryMass, separatorCharge]
      omega
private theorem EdgeRestrictedStoppedRecursion.sum_propagatedBoundary_card_eq_mass
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) (boundary : Finset ι) :
    (∑ owner : tree.edgeOwnerType, (tree.propagatedBoundary boundary owner).card) =
      tree.propagatedBoundaryMass boundary := by
  classical
  induction tree generalizing boundary with
  | @leaf edges vertices hsubset hsymmetric hincident hcard =>
      let root := EdgeRestrictedStoppedRecursion.leaf hsubset hsymmetric hincident hcard
      have hFintype : EdgeRestrictedStoppedRecursion.edgeOwnerFintype root =
          (inferInstance : Fintype Unit) := Subsingleton.elim _ _
      rw [hFintype]
      simp [edgeOwnerType, propagatedBoundary, propagatedBoundaryMass]
  | @split edges vertices left separator right hsubset hsymmetric hincident hpartition
      hminimum hleft hright leftTree rightTree ihLeft ihRight =>
      let root := EdgeRestrictedStoppedRecursion.split hsubset hsymmetric hincident hpartition
        hminimum hleft hright leftTree rightTree
      let sumFintype : Fintype (Sum leftTree.edgeOwnerType rightTree.edgeOwnerType) :=
        instFintypeSum _ _
      have hFintype : EdgeRestrictedStoppedRecursion.edgeOwnerFintype root = sumFintype :=
        Subsingleton.elim _ _
      rw [hFintype]
      simp [edgeOwnerType, propagatedBoundary, propagatedBoundaryMass,
        Fintype.sum_sum_type, ihLeft, ihRight]
private theorem EdgeRestrictedStoppedRecursion.inheritedAncestorBoundary_subset_propagated
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (boundary : Finset ι) (owner : tree.edgeOwnerType) :
    (boundary ∪ tree.edgeOwnerAncestors owner) ∩
        edgeIncidentVertices (tree.edgeRegion owner) ⊆
      tree.propagatedBoundary boundary owner := by
  classical
  induction tree generalizing boundary with
  | leaf _ _ _ _ => simp [edgeOwnerAncestors, edgeRegion, propagatedBoundary]
  | @split edges vertices left separator right hsubset hsymmetric hincident hpartition
      hminimum hleft hright leftTree rightTree ihLeft ihRight =>
      cases owner with
      | inl owner =>
          intro x hx
          have hxIncident : x ∈ edgeIncidentVertices (leftTree.edgeRegion owner) := by
            simpa [edgeRegion] using (Finset.mem_inter.mp hx).2
          have hxCarrier : x ∈ left ∪ separator := by
            exact separatorLeftEdges_incident_subset G edges vertices left separator right
              hsubset hsymmetric hincident hpartition
              (edgeIncidentVertices_mono (leftTree.edgeRegion_subset owner) hxIncident)
          have hxUnion : x ∈ leftRefinedBoundary boundary left separator ∪
              leftTree.edgeOwnerAncestors owner := by
            rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with
              hxBoundary | hxAncestor
            · have hxChildBoundary : x ∈ leftRefinedBoundary boundary left separator := by
                simp only [leftRefinedBoundary, Finset.mem_union]
                exact Or.inr (Finset.mem_inter.mpr ⟨hxBoundary, hxCarrier⟩)
              exact Finset.mem_union_left _ hxChildBoundary
            · rcases Finset.mem_union.mp hxAncestor with hxSeparator | hxChildAncestor
              · exact Finset.mem_union_left _
                  (separator_subset_leftRefinedBoundary boundary left separator hxSeparator)
              · exact Finset.mem_union_right _ hxChildAncestor
          exact ihLeft (leftRefinedBoundary boundary left separator) owner
            (Finset.mem_inter.mpr ⟨hxUnion, hxIncident⟩)
      | inr owner =>
          intro x hx
          have hxIncident : x ∈ edgeIncidentVertices (rightTree.edgeRegion owner) := by
            simpa [edgeRegion] using (Finset.mem_inter.mp hx).2
          have hxCarrier : x ∈ right ∪ separator := by
            exact separatorRightEdges_incident_subset G edges vertices left separator right
              hsubset hsymmetric hincident hpartition
              (edgeIncidentVertices_mono (rightTree.edgeRegion_subset owner) hxIncident)
          have hxUnion : x ∈ rightRefinedBoundary boundary right separator ∪
              rightTree.edgeOwnerAncestors owner := by
            rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with
              hxBoundary | hxAncestor
            · have hxChildBoundary : x ∈ rightRefinedBoundary boundary right separator := by
                simp only [rightRefinedBoundary, Finset.mem_union]
                exact Or.inr (Finset.mem_inter.mpr ⟨hxBoundary, hxCarrier⟩)
              exact Finset.mem_union_left _ hxChildBoundary
            · rcases Finset.mem_union.mp hxAncestor with hxSeparator | hxChildAncestor
              · exact Finset.mem_union_left _
                  (separator_subset_rightRefinedBoundary boundary right separator hxSeparator)
              · exact Finset.mem_union_right _ hxChildAncestor
          exact ihRight (rightRefinedBoundary boundary right separator) owner
            (Finset.mem_inter.mpr ⟨hxUnion, hxIncident⟩)
private theorem EdgeRestrictedStoppedRecursion.terminalBoundaryMass_le_three_charge
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices) :
    tree.terminalBoundaryMass ≤ 3 * tree.separatorCharge := by
  classical
  calc
    tree.terminalBoundaryMass =
        ∑ owner : tree.edgeOwnerType, (tree.terminalBoundary owner).card := rfl
    _ ≤ ∑ owner : tree.edgeOwnerType,
        (tree.propagatedBoundary ∅ owner).card := by
      exact Finset.sum_le_sum fun owner _ => Finset.card_le_card (by
        intro x hx
        apply tree.inheritedAncestorBoundary_subset_propagated ∅ owner
        simpa [terminalBoundary] using hx)
    _ = tree.propagatedBoundaryMass ∅ :=
      tree.sum_propagatedBoundary_card_eq_mass ∅
    _ ≤ (∅ : Finset ι).card + 3 * tree.separatorCharge :=
      tree.propagatedBoundaryMass_le ∅
    _ = 3 * tree.separatorCharge := by simp
private theorem EdgeRestrictedStoppedRecursion.refinedEdgeActive_mul_scale_le_root
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hstopped : tree.StoppedAtScale)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 1 ≤ r) (hthreshold : profileDivisionThreshold beta exponent ≤ r)
    (hlower : r ≤ 4 * vertices.card) :
    (((tree.refinedEdgeActive beta exponent hProfile).card * r : Nat) : ℝ) ≤
      profileDivisionRegionConstant beta exponent * vertices.card := by
  let budget := weightedSpineSeparatorBudget beta exponent r
  let potentialCoefficient := profileDivisionPotentialCoefficient beta exponent
  let quarterPower := (1 / 4 : ℝ) ^ (1 - exponent)
  let weightedCoefficient := beta / (1 - markedSpineDecayRatio exponent)
  have hrPos : 0 < r := Nat.zero_lt_of_lt hr
  have hbudgetPosNat : 0 < budget :=
    weightedSpineSeparatorBudget_pos hProfile.1 hexponent.1 hr
  have hbudgetPos : (0 : ℝ) < budget := by exact_mod_cast hbudgetPosNat
  have hquarterPos : 0 < quarterPower := by
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hweightedPos : 0 < weightedCoefficient := by
    exact div_pos (zero_lt_one.trans_le hProfile.1)
      (sub_pos.mpr (markedSpineDecayRatio_lt_one hexponent.1))
  have hbudgetLower : weightedCoefficient * (r : ℝ) ^ exponent ≤ budget := by
    dsimp [budget, weightedCoefficient, weightedSpineSeparatorBudget]
    exact_mod_cast (Nat.le_ceil
      (beta / (1 - markedSpineDecayRatio exponent) * (r : ℝ) ^ exponent))
  have hchargePotential := tree.separatorCharge_le_potential hstopped beta exponent
    hProfile hexponent hrPos hthreshold hlower
  have hpotentialRoot := profileDivisionPotential_le_root
    (zero_le_one.trans hProfile.1) hexponent hr
    (r := r) (parent := vertices.card)
  have hchargeRoot : (tree.separatorCharge : ℝ) ≤
      profileDivisionChargeRootConstant beta exponent * vertices.card := by
    push_cast at hchargePotential
    calc
      (tree.separatorCharge : ℝ) ≤
          profileDivisionPotential beta exponent r vertices.card / 3 := by
        linarith
      _ ≤ (profileDivisionPotentialCoefficient beta exponent /
          (1 / 4 : ℝ) ^ (1 - exponent) * vertices.card) / 3 :=
        div_le_div_of_nonneg_right hpotentialRoot (by norm_num)
      _ = profileDivisionChargeRootConstant beta exponent * vertices.card := by
        unfold profileDivisionChargeRootConstant
        field_simp [hquarterPos.ne']
  have hboundaryPotential : (tree.terminalBoundaryMass : ℝ) ≤
      profileDivisionPotential beta exponent r vertices.card := by
    have hboundary := tree.terminalBoundaryMass_le_three_charge
    have hboundaryReal : (tree.terminalBoundaryMass : ℝ) ≤
        3 * tree.separatorCharge := by exact_mod_cast hboundary
    have hcharge := hchargePotential
    push_cast at hcharge
    linarith [hboundaryReal]
  have hpotentialLinear := profileDivisionPotential_le_linear
    (zero_le_one.trans hProfile.1) hexponent hrPos
    (r := r) (parent := vertices.card)
  have hrpowIdentity :
      (r : ℝ) * (r : ℝ) ^ (exponent - 1) = (r : ℝ) ^ exponent := by
    rw [Real.rpow_sub_one (by positivity)]
    field_simp [show (r : ℝ) ≠ 0 by positivity]
  have hboundaryRatio :
      (r : ℝ) * tree.terminalBoundaryMass / budget ≤
        profileDivisionBoundaryRatioConstant beta exponent * vertices.card := by
    have hnumerator :
        (r : ℝ) * tree.terminalBoundaryMass ≤
          (potentialCoefficient / quarterPower) * vertices.card * (r : ℝ) ^ exponent := by
      have hboundaryLinear := hboundaryPotential.trans hpotentialLinear
      have hscaledLinear := mul_le_mul_of_nonneg_left hboundaryLinear
        (Nat.cast_nonneg r)
      calc
        (r : ℝ) * tree.terminalBoundaryMass ≤
            (r : ℝ) * (profileDivisionPotentialCoefficient beta exponent *
              (vertices.card * (r : ℝ) ^ (exponent - 1) /
                (1 / 4 : ℝ) ^ (1 - exponent))) := hscaledLinear
        _ = (potentialCoefficient / quarterPower) * vertices.card *
            (r : ℝ) ^ exponent := by
          rw [← hrpowIdentity]
          dsimp [potentialCoefficient, quarterPower]
          ring
    apply (div_le_iff₀ hbudgetPos).2
    calc
      (r : ℝ) * tree.terminalBoundaryMass ≤
          (potentialCoefficient / quarterPower) * vertices.card * (r : ℝ) ^ exponent :=
        hnumerator
      _ = profileDivisionBoundaryRatioConstant beta exponent * vertices.card *
          (weightedCoefficient * (r : ℝ) ^ exponent) := by
        change (potentialCoefficient / quarterPower) * vertices.card *
            (r : ℝ) ^ exponent =
          (potentialCoefficient / (quarterPower * weightedCoefficient)) * vertices.card *
            (weightedCoefficient * (r : ℝ) ^ exponent)
        field_simp [hquarterPos.ne', hweightedPos.ne']
      _ ≤ profileDivisionBoundaryRatioConstant beta exponent * vertices.card * budget := by
        apply mul_le_mul_of_nonneg_left hbudgetLower
        have hconstantNonneg : 0 ≤ profileDivisionBoundaryRatioConstant beta exponent := by
          unfold profileDivisionBoundaryRatioConstant
          exact div_nonneg
            (profileDivisionPotentialCoefficient_nonneg
              (zero_le_one.trans hProfile.1) hexponent)
            (mul_nonneg hquarterPos.le hweightedPos.le)
        exact mul_nonneg hconstantNonneg (Nat.cast_nonneg vertices.card)
  have hleaf := tree.terminalOwnerCount_mul_scale_le_four_carrierMass hstopped hlower
  have hcarrier := tree.terminalCarrierMass_le_root_add_charge
  have hleafRoot : (tree.terminalOwnerCount : ℝ) * r ≤
      (4 + 4 * profileDivisionChargeRootConstant beta exponent) * vertices.card := by
    have hleafReal : (tree.terminalOwnerCount : ℝ) * r ≤
        4 * tree.terminalCarrierMass := by exact_mod_cast hleaf
    have hcarrierReal : (tree.terminalCarrierMass : ℝ) ≤
        vertices.card + tree.separatorCharge := by exact_mod_cast hcarrier
    calc
      (tree.terminalOwnerCount : ℝ) * r ≤ 4 * tree.terminalCarrierMass := hleafReal
      _ ≤ 4 * ((vertices.card : ℝ) + tree.separatorCharge) := by
        exact mul_le_mul_of_nonneg_left hcarrierReal (by norm_num)
      _ ≤ 4 * ((vertices.card : ℝ) +
          profileDivisionChargeRootConstant beta exponent * vertices.card) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (le_refl (vertices.card : ℝ)) hchargeRoot) (by norm_num)
      _ = (4 + 4 * profileDivisionChargeRootConstant beta exponent) * vertices.card := by
        ring
  have hrefined := tree.refinedEdgeActive_card_mul_budget_le beta exponent hProfile
  have hrefinedReal : ((tree.refinedEdgeActive beta exponent hProfile).card : ℝ) ≤
      tree.terminalOwnerCount + 2 * tree.terminalBoundaryMass / budget := by
    have hrefinedCast :
        ((tree.refinedEdgeActive beta exponent hProfile).card : ℝ) * budget ≤
          tree.terminalOwnerCount * budget + 2 * tree.terminalBoundaryMass := by
      exact_mod_cast hrefined
    calc
      ((tree.refinedEdgeActive beta exponent hProfile).card : ℝ) ≤
          (tree.terminalOwnerCount * budget + 2 * tree.terminalBoundaryMass) / budget :=
        (le_div_iff₀ hbudgetPos).2 hrefinedCast
      _ = tree.terminalOwnerCount + 2 * tree.terminalBoundaryMass / budget := by
        field_simp [hbudgetPos.ne']
  have hrNonneg : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hscaled := mul_le_mul_of_nonneg_right hrefinedReal hrNonneg
  push_cast
  calc
    ((tree.refinedEdgeActive beta exponent hProfile).card : ℝ) * r ≤
        (tree.terminalOwnerCount : ℝ) * r +
          2 * ((r : ℝ) * (tree.terminalBoundaryMass : ℝ) / budget) := by
      have hdecompose :
          ((tree.terminalOwnerCount : ℝ) +
              2 * (tree.terminalBoundaryMass : ℝ) / (budget : ℝ)) * (r : ℝ) =
            (tree.terminalOwnerCount : ℝ) * r +
              2 * ((r : ℝ) * (tree.terminalBoundaryMass : ℝ) / budget) := by
        ring
      exact hscaled.trans_eq hdecompose
    _ ≤ (4 + 4 * profileDivisionChargeRootConstant beta exponent) * vertices.card +
        2 * (profileDivisionBoundaryRatioConstant beta exponent * vertices.card) :=
      add_le_add hleafRoot (mul_le_mul_of_nonneg_left hboundaryRatio (by norm_num))
    _ = profileDivisionRegionConstant beta exponent * vertices.card := by
      unfold profileDivisionRegionConstant
      ring
end QEC.Locality
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace EdgeRestrictedStoppedRecursion
theorem _root_.solution
    {G : ConnectivityGraph ι} {r : Nat} {edges : Finset (ι × ι)} {vertices : Finset ι}
    (tree : EdgeRestrictedStoppedRecursion G r edges vertices)
    (hstopped : tree.StoppedAtScale)
    (beta exponent : ℝ)
    (hProfile : AssumedBGKLMeasuredProfilePowerUpperBound G beta exponent)
    (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 1 ≤ r) (hthreshold : profileDivisionThreshold beta exponent ≤ r)
    (hlower : r ≤ 4 * vertices.card) :
    (tree.refinedEdgeActive beta exponent hProfile).card ≤
      Nat.ceil (profileDivisionRegionConstant beta exponent * vertices.card / r) := by
  have hscaled := tree.refinedEdgeActive_mul_scale_le_root hstopped beta exponent
    hProfile hexponent hr hthreshold hlower
  have hrReal : (0 : ℝ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hratio : ((tree.refinedEdgeActive beta exponent hProfile).card : ℝ) ≤
      profileDivisionRegionConstant beta exponent * vertices.card / r := by
    apply (le_div_iff₀ hrReal).2
    simpa [Nat.cast_mul] using hscaled
  exact_mod_cast hratio.trans (Nat.le_ceil _)
end EdgeRestrictedStoppedRecursion
end QEC.Locality
