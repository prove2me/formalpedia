-- Prove2me | solution 1 for QEC.Locality.exists_erasureRecovery_of_pairwise_fixedGeneratorDecoupled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:24:03.551633+00:00
-- url     : https://prove2.me/submissions/024df0b9-f9a1-4b4f-b308-9f689d48ed1f

import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_fixedGeneratorDecoupled
import Theorems.Thm_QEC_Locality_exists_erasureRecovery_of_localPauli_pair_criterion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Coding_StabilizerCode_vector_mem_generatedVectorSubspace_iff
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



set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {κ : Type v} [Fintype κ] {α : Type w} [DecidableEq α]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (regions : α → FiniteSubsystem ι) (s : Finset α)
    (hRecovery : ∀ a, a ∈ s →
      ∃ recovery : QuantumChannel (regions a).complementSystem (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι) (regions a).complementSystem P.semanticCode
          (regions a).erasureChannelFromRegister recovery)
    (hDecoupled : ∀ a, a ∈ s → ∀ b, b ∈ s → a ≠ b →
      P.fixedGeneratorDecoupled ((regions a).selected : Set ι) ((regions b).selected : Set ι)) :
    ∃ recovery : QuantumChannel (familyUnionSubsystem regions s).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι) (familyUnionSubsystem regions s).complementSystem
        P.semanticCode (familyUnionSubsystem regions s).erasureChannelFromRegister recovery := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      apply exists_erasureRecovery_of_localPauli_pair_criterion P
        (familyUnionSubsystem regions ∅)
      intro p q _ _
      have hEmpty : IsEmpty (familyUnionSubsystem regions ∅).SelectedCoordinates := by
        constructor
        intro i
        rcases Finset.mem_biUnion.mp i.property with ⟨a, ha, _⟩
        simp at ha
      have hsubsingleton : Subsingleton (LocalPauliWordIndex (familyUnionSubsystem regions ∅)) := by
        constructor
        intro x y
        apply Prod.ext <;> funext i
        · exact (hEmpty.false i).elim
        · exact (hEmpty.false i).elim
      have hpq : p = q := hsubsingleton.elim _ _
      subst q
      left
      apply (StabilizerCode.vector_mem_generatedVectorSubspace_iff P.code.1 _).1
      change (0 : SymplecticVector (ZMod 2) ι) ∈ P.code.1.generatedVectorSubspace
      exact P.code.1.generatedVectorSubspace.zero_mem
  | @insert a s haNotMem ih =>
      have hRecoveryTail : ∀ b, b ∈ s →
          ∃ recovery : QuantumChannel (regions b).complementSystem (Qubit.QubitRegister ι),
            Correctable (Qubit.QubitRegister ι) (regions b).complementSystem P.semanticCode
              (regions b).erasureChannelFromRegister recovery := by
        intro b hb
        exact hRecovery b (Finset.mem_insert_of_mem hb)
      have hDecoupledTail : ∀ b, b ∈ s → ∀ c, c ∈ s → b ≠ c →
          P.fixedGeneratorDecoupled ((regions b).selected : Set ι) ((regions c).selected : Set ι) := by
        intro b hb c hc hbc
        exact hDecoupled b (Finset.mem_insert_of_mem hb)
          c (Finset.mem_insert_of_mem hc) hbc
      rcases hRecovery a (Finset.mem_insert_self a s) with ⟨recoveryA, hRecoveryA⟩
      rcases ih hRecoveryTail hDecoupledTail with ⟨recoveryB, hRecoveryB⟩
      have hHeadTail : P.fixedGeneratorDecoupled ((regions a).selected : Set ι)
          ((familyUnionSubsystem regions s).selected : Set ι) := by
        constructor
        · apply Set.disjoint_left.mpr
          intro x hxA hxTail
          rcases Finset.mem_biUnion.mp (by simpa [familyUnionSubsystem] using hxTail) with
            ⟨b, hb, hxb⟩
          have hab : a ≠ b := by
            intro hab
            subst b
            exact haNotMem hb
          exact (Set.disjoint_left.mp
            (hDecoupled a (Finset.mem_insert_self a s) b
              (Finset.mem_insert_of_mem hb) hab).1) hxA (by simpa using hxb)
        · intro x hxA y hxTail hxy
          rcases Finset.mem_biUnion.mp (by simpa [familyUnionSubsystem] using hxTail) with
            ⟨b, hb, hyb⟩
          have hab : a ≠ b := by
            intro hab
            subst b
            exact haNotMem hb
          exact (hDecoupled a (Finset.mem_insert_self a s) b
            (Finset.mem_insert_of_mem hb) hab).2 hxA (by simpa using hyb) hxy
      have hUnion : familyUnionSubsystem regions (insert a s) =
          unionSubsystem (regions a) (familyUnionSubsystem regions s) := by
        simp only [familyUnionSubsystem, unionSubsystem, Finset.biUnion_insert]
      rw [hUnion]
      exact exists_erasureRecovery_of_fixedGeneratorDecoupled P (regions a)
        (familyUnionSubsystem regions s) recoveryA recoveryB hRecoveryA hRecoveryB hHeadTail
end QEC.Locality
