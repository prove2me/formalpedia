-- Prove2me | solution 1 for QEC.Locality.bkSumPreservingRecurrence_le_coefficient_mul_scale_mul_depth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:30:21.514759+00:00
-- url     : https://prove2.me/submissions/d074c683-bc5b-4c8b-b7b8-5151e75cab45

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_eq_zero_of_terminal
import Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_eq_profile_add
import Theorems.Thm_QEC_Locality_bkTwoThirdsDepth_eq_succ
import Theorems.Thm_QEC_Locality_bkTwoThirdsDepth_mono
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
import Theorems.Thm_QEC_Locality_card_le_bkTwoThirdsChildScale
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
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (d coefficient parent : Nat)
    (hprofile : ∀ scale : Nat, d ≤ scale →
      twoThirdsSeparationProfile G scale ≤ coefficient * scale) :
    bkSumPreservingRecurrence G d parent ≤
      coefficient * parent * bkTwoThirdsDepth d parent := by
  induction parent using Nat.strong_induction_on with
  | h parent ih =>
      by_cases hterminal : bkScaleTerminal d parent
      · rw [bkSumPreservingRecurrence_eq_zero_of_terminal G d parent hterminal]
        exact Nat.zero_le _
      · have hparentPositive : 0 < parent := by
          by_contra hpositive
          apply hterminal
          exact Or.inl (Nat.eq_zero_of_not_pos hpositive)
        have hdparent : d ≤ parent := by
          by_contra hd
          exact hterminal (Or.inr (by omega))
        have hchildScaleLt : bkTwoThirdsChildScale parent < parent :=
          bkTwoThirdsChildScale_lt parent hparentPositive
        have hsup :
            (bkAdmissibleChildPairs parent).sup (fun children =>
                if hchildren : children ∈ bkAdmissibleChildPairs parent then
                  bkSumPreservingRecurrence G d children.1 +
                    bkSumPreservingRecurrence G d children.2
                else 0) ≤
              coefficient * parent * bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) := by
          apply Finset.sup_le
          intro children hchildren
          simp only [dif_pos hchildren]
          have hadmissible := (mem_bkAdmissibleChildPairs_iff).1 hchildren
          have hleftBound := ih children.1 hadmissible.1
          have hrightBound := ih children.2 hadmissible.2.1
          have hleftScale : children.1 ≤ bkTwoThirdsChildScale parent :=
            card_le_bkTwoThirdsChildScale hadmissible.2.2.2.1
          have hrightScale : children.2 ≤ bkTwoThirdsChildScale parent :=
            card_le_bkTwoThirdsChildScale hadmissible.2.2.2.2
          have hleftDepth := bkTwoThirdsDepth_mono d hleftScale
          have hrightDepth := bkTwoThirdsDepth_mono d hrightScale
          calc
            bkSumPreservingRecurrence G d children.1 +
                bkSumPreservingRecurrence G d children.2
                ≤ coefficient * children.1 * bkTwoThirdsDepth d children.1 +
                    coefficient * children.2 * bkTwoThirdsDepth d children.2 :=
              Nat.add_le_add hleftBound hrightBound
            _ ≤ coefficient * children.1 * bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) +
                  coefficient * children.2 * bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) := by
              exact Nat.add_le_add
                (Nat.mul_le_mul_left (coefficient * children.1) hleftDepth)
                (Nat.mul_le_mul_left (coefficient * children.2) hrightDepth)
            _ = coefficient * (children.1 + children.2) *
                  bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) := by
              ring
            _ ≤ coefficient * parent *
                  bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) := by
              exact Nat.mul_le_mul_right _
                (Nat.mul_le_mul_left coefficient hadmissible.2.2.1)
        rw [bkSumPreservingRecurrence_eq_profile_add G d parent hterminal]
        rw [bkTwoThirdsDepth_eq_succ d parent hterminal]
        calc
          twoThirdsSeparationProfile G parent +
              (bkAdmissibleChildPairs parent).sup (fun children =>
                if hchildren : children ∈ bkAdmissibleChildPairs parent then
                  bkSumPreservingRecurrence G d children.1 +
                    bkSumPreservingRecurrence G d children.2
                else 0)
              ≤ coefficient * parent +
                  coefficient * parent *
                    bkTwoThirdsDepth d (bkTwoThirdsChildScale parent) :=
            Nat.add_le_add (hprofile parent hdparent) hsup
          _ = coefficient * parent *
                (1 + bkTwoThirdsDepth d (bkTwoThirdsChildScale parent)) := by
            ring
end QEC.Locality
