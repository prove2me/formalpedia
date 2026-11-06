-- Prove2me | solution 1 for QEC.Locality.bkSumPreservingRecurrence_cast_le_bkRpowPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:35:32.9082+00:00
-- url     : https://prove2.me/submissions/2f08d953-3fb1-4558-8f8c-8e4de59b3504

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Theorems.Thm_QEC_Locality_exists_saturated_bkAdmissibleChildPair
import Theorems.Thm_QEC_Locality_bkRpowPotential_nonneg_of_lower_scale
import Theorems.Thm_QEC_Locality_add_bkRpowPotential_children_le_parent
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_eq_profile_add
import Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_eq_zero_of_terminal
import Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_mono
import Theorems.Thm_QEC_Locality_zero_zero_mem_bkAdmissibleChildPairs
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
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (d root parent : Nat) (beta c : ℝ)
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) (hd : 2 ≤ d)
    (hparent : d ≤ parent) (hroot : parent ≤ root)
    (hprofile : ∀ scale : Nat, d ≤ scale → scale ≤ root →
      (twoThirdsSeparationProfile G scale : ℝ) ≤ beta * (scale : ℝ) ^ c) :
    (bkSumPreservingRecurrence G d parent : ℝ) ≤
      bkRpowPotential beta c d parent := by
  induction parent using Nat.strong_induction_on with
  | h parent ih =>
      have hdPos : 0 < d := by omega
      have hparentPos : 0 < parent := by omega
      have hnonterminal : ¬bkScaleTerminal d parent := by
        unfold bkScaleTerminal
        omega
      have hpairs : (bkAdmissibleChildPairs parent).Nonempty :=
        ⟨(0, 0), zero_zero_mem_bkAdmissibleChildPairs hparentPos⟩
      let childCost : Nat × Nat → Nat := fun children ↦
        if hchildren : children ∈ bkAdmissibleChildPairs parent then
          bkSumPreservingRecurrence G d children.1 +
            bkSumPreservingRecurrence G d children.2
        else 0
      obtain ⟨children, hchildren, hsup⟩ :=
        Finset.exists_mem_eq_sup (bkAdmissibleChildPairs parent) hpairs childCost
      obtain ⟨saturated, hleftMono, hrightMono, hsum,
          hsatLeftLower, hsatRightLower, hsatLeftUpper, hsatRightUpper,
          hsatLeftLt, hsatRightLt⟩ :=
        exists_saturated_bkAdmissibleChildPair
          (hparent.trans' hd) hchildren
      have hsaturatedLeftBound :
          (bkSumPreservingRecurrence G d saturated.1 : ℝ) ≤
            bkRpowPotential beta c d saturated.1 := by
        by_cases hterminal : bkScaleTerminal d saturated.1
        · rw [bkSumPreservingRecurrence_eq_zero_of_terminal G d saturated.1 hterminal]
          simpa only [Nat.cast_zero] using
            bkRpowPotential_nonneg_of_lower_scale hbeta hc0 hc1 hdPos
              (hparent.trans hsatLeftLower)
        · have hdsaturated : d ≤ saturated.1 := by
            unfold bkScaleTerminal at hterminal
            omega
          exact ih saturated.1 hsatLeftLt hdsaturated
            ((Nat.le_of_lt hsatLeftLt).trans hroot)
      have hsaturatedRightBound :
          (bkSumPreservingRecurrence G d saturated.2 : ℝ) ≤
            bkRpowPotential beta c d saturated.2 := by
        by_cases hterminal : bkScaleTerminal d saturated.2
        · rw [bkSumPreservingRecurrence_eq_zero_of_terminal G d saturated.2 hterminal]
          simpa only [Nat.cast_zero] using
            bkRpowPotential_nonneg_of_lower_scale hbeta hc0 hc1 hdPos
              (hparent.trans hsatRightLower)
        · have hdsaturated : d ≤ saturated.2 := by
            unfold bkScaleTerminal at hterminal
            omega
          exact ih saturated.2 hsatRightLt hdsaturated
            ((Nat.le_of_lt hsatRightLt).trans hroot)
      have hleftRecurrenceMono :
          (bkSumPreservingRecurrence G d children.1 : ℝ) ≤
            bkSumPreservingRecurrence G d saturated.1 := by
        exact_mod_cast bkSumPreservingRecurrence_mono G d hleftMono
      have hrightRecurrenceMono :
          (bkSumPreservingRecurrence G d children.2 : ℝ) ≤
            bkSumPreservingRecurrence G d saturated.2 := by
        exact_mod_cast bkSumPreservingRecurrence_mono G d hrightMono
      have hcharge := hprofile parent hparent hroot
      have hclose := add_bkRpowPotential_children_le_parent G
        hbeta hc0 hc1 hdPos hparentPos hsum hsatLeftLower hsatLeftUpper hcharge
      rw [bkSumPreservingRecurrence_eq_profile_add G d parent hnonterminal]
      change ((twoThirdsSeparationProfile G parent +
        (bkAdmissibleChildPairs parent).sup childCost : Nat) : ℝ) ≤ _
      rw [hsup]
      simp only [childCost, dif_pos hchildren, Nat.cast_add]
      linarith
end QEC.Locality
