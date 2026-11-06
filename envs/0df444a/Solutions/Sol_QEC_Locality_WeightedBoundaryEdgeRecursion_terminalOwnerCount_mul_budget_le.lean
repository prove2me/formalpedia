-- Prove2me | solution 1 for QEC.Locality.WeightedBoundaryEdgeRecursion.terminalOwnerCount_mul_budget_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:43:24.601939+00:00
-- url     : https://prove2.me/submissions/b5f43724-2f30-4437-85c1-1b8a397f7247

import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedRecursion
import Definitions.Def_QEC_Locality_SeparatorProfile_Weighted
import Definitions.Def_QEC_Locality_SeparatorProfile_WeightedRefinement
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_disjoint_stopSides
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_marked_light
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_exposedSide_stop
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_stopSides_disjoint
import Theorems.Thm_QEC_Locality_MarkedSeparatorSpine_stopSides_marked_light
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
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
private theorem WeightedBoundaryEdgeRecursion.terminalOwnerCount_eq_one_add_two_mul_splitCount
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    tree.terminalOwnerCount = 1 + 2 * tree.splitCount := by
  induction tree with
  | leaf _ _ _ _ _ _ => rfl
  | split _ _ _ _ _ _ _ _ firstTree secondTree thirdTree ihFirst ihSecond ihThird =>
      simp only [terminalOwnerCount, splitCount]
      omega
private theorem three_inter_card_sum_le
    (boundary first second third : Finset ι)
    (hfirstSecond : Disjoint first second) (hfirstThird : Disjoint first third)
    (hsecondThird : Disjoint second third) :
    (boundary ∩ first).card + (boundary ∩ second).card + (boundary ∩ third).card ≤
      boundary.card := by
  let firstPart := boundary ∩ first
  let secondPart := boundary ∩ second
  let thirdPart := boundary ∩ third
  have h12 : Disjoint firstPart secondPart := by
    apply Finset.disjoint_left.mpr
    intro x hxFirst hxSecond
    exact (Finset.disjoint_left.mp hfirstSecond)
      (Finset.mem_inter.mp hxFirst).2 (Finset.mem_inter.mp hxSecond).2
  have h13 : Disjoint firstPart thirdPart := by
    apply Finset.disjoint_left.mpr
    intro x hxFirst hxThird
    exact (Finset.disjoint_left.mp hfirstThird)
      (Finset.mem_inter.mp hxFirst).2 (Finset.mem_inter.mp hxThird).2
  have h23 : Disjoint secondPart thirdPart := by
    apply Finset.disjoint_left.mpr
    intro x hxSecond hxThird
    exact (Finset.disjoint_left.mp hsecondThird)
      (Finset.mem_inter.mp hxSecond).2 (Finset.mem_inter.mp hxThird).2
  have hunionDisjoint : Disjoint (firstPart ∪ secondPart) thirdPart :=
    Finset.disjoint_union_left.mpr ⟨h13, h23⟩
  have hunionSubset : firstPart ∪ secondPart ∪ thirdPart ⊆ boundary := by
    exact Finset.union_subset (Finset.union_subset Finset.inter_subset_left
      Finset.inter_subset_left) Finset.inter_subset_left
  calc
    firstPart.card + secondPart.card + thirdPart.card =
        (firstPart ∪ secondPart ∪ thirdPart).card := by
      symm
      rw [Finset.card_union_of_disjoint hunionDisjoint,
        Finset.card_union_of_disjoint h12]
    _ ≤ boundary.card := Finset.card_le_card hunionSubset
private theorem WeightedBoundaryEdgeRecursion.splitCount_zero_or_mul_add_three_le_boundary
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    tree.splitCount = 0 ∨ (tree.splitCount + 3) * spineBudget ≤ boundary.card := by
  induction tree with
  | leaf _ _ _ _ _ _ => exact Or.inl rfl
  | @split edges vertices boundary hsubset hsymmetric hincident hboundary hcard spine
      hseparatorCard hboundaryLarge firstTree secondTree thirdTree
      ihFirst ihSecond ihThird =>
      right
      have hfirstCard := weightedSpineChildBoundary_card_le boundary spine.exposedSide
        (markedSpineSeparatorUnion spine)
      have hsecondCard := weightedSpineChildBoundary_card_le boundary spine.stopSides.1
        (markedSpineSeparatorUnion spine)
      have hthirdCard := weightedSpineChildBoundary_card_le boundary spine.stopSides.2
        (markedSpineSeparatorUnion spine)
      have hparts := three_inter_card_sum_le boundary spine.exposedSide spine.stopSides.1
        spine.stopSides.2 spine.exposedSide_disjoint_stopSides.1
        spine.exposedSide_disjoint_stopSides.2 spine.stopSides_disjoint
      have hfirstLight : 3 * (boundary ∩ spine.exposedSide).card ≤ 2 * boundary.card :=
        spine.exposedSide_marked_light
      have hstopLight := spine.stopSides_marked_light
      rcases ihFirst with hfirstZero | hfirstCharge <;>
        rcases ihSecond with hsecondZero | hsecondCharge <;>
        rcases ihThird with hthirdZero | hthirdCharge
      · simp only [splitCount, hfirstZero, hsecondZero, hthirdZero, zero_add,
          add_zero, Nat.add_mul, Nat.one_mul]
        omega
      · simp only [splitCount, hfirstZero, hsecondZero, zero_add, add_zero,
          Nat.add_mul, Nat.one_mul] at hthirdCharge ⊢
        omega
      · simp only [splitCount, hfirstZero, hthirdZero, zero_add, add_zero,
          Nat.add_mul, Nat.one_mul] at hsecondCharge ⊢
        omega
      · simp only [splitCount, hfirstZero, zero_add, add_zero,
          Nat.add_mul, Nat.one_mul] at hsecondCharge hthirdCharge ⊢
        omega
      · simp only [splitCount, hsecondZero, hthirdZero, zero_add, add_zero,
          Nat.add_mul, Nat.one_mul] at hfirstCharge ⊢
        omega
      · simp only [splitCount, hsecondZero, zero_add, add_zero,
          Nat.add_mul, Nat.one_mul] at hfirstCharge hthirdCharge ⊢
        omega
      · simp only [splitCount, hthirdZero, zero_add, add_zero,
          Nat.add_mul, Nat.one_mul] at hfirstCharge hsecondCharge ⊢
        omega
      · simp only [splitCount, Nat.add_mul, Nat.one_mul] at hfirstCharge hsecondCharge hthirdCharge ⊢
        omega
private theorem WeightedBoundaryEdgeRecursion.splitCount_mul_budget_le_boundary
    {G : ConnectivityGraph ι} {r spineBudget : Nat}
    {edges : Finset (ι × ι)} {vertices boundary : Finset ι}
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    tree.splitCount * spineBudget ≤ boundary.card := by
  rcases tree.splitCount_zero_or_mul_add_three_le_boundary with hzero | hcharge
  · simp [hzero]
  · exact (Nat.mul_le_mul_right spineBudget (Nat.le_add_right tree.splitCount 3)).trans hcharge
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
    (tree : WeightedBoundaryEdgeRecursion G r spineBudget edges vertices boundary) :
    tree.terminalOwnerCount * spineBudget ≤ spineBudget + 2 * boundary.card := by
  rw [tree.terminalOwnerCount_eq_one_add_two_mul_splitCount, Nat.add_mul, Nat.one_mul]
  have hcharge := Nat.mul_le_mul_left 2 tree.splitCount_mul_budget_le_boundary
  simpa [Nat.mul_assoc] using Nat.add_le_add_left hcharge spineBudget
end WeightedBoundaryEdgeRecursion
end QEC.Locality
