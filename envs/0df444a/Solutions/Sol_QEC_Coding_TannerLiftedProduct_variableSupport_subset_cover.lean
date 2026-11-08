-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.variableSupport_subset_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:14:56.063674+00:00
-- url     : https://prove2.me/submissions/f6409bad-5e2b-464a-816c-a32216b415dd

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldCSSPresentation
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_doubleCoverTannerMatrix_coeff_ne_zero_iff
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
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
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.LiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (q : LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G) :
    (LiftedProduct.boundaryIncidence (data label h g')).variableSupport q ⊆
      variableSupportCover label h g' q := by
  classical
  intro c hc
  rw [QEC.QLDPC.CheckIncidence.mem_variableSupport] at hc
  rw [← QEC.QLDPC.CheckIncidence.mem_checkSupport] at hc
  cases q with
  | inl q =>
      rcases q with ⟨ac, br, gi⟩
      cases c with
      | inl c0 =>
          rcases c0 with ⟨ar, br', go⟩
          rw [LiftedProduct.boundaryIncidence_checkSupport_inl,
            LiftedProduct.mem_boundary1RowSupport_inl] at hc
          rcases hc with ⟨rfl, hCoeff⟩
          rw [data, doubleCoverTannerMatrix_coeff_ne_zero_iff] at hCoeff
          have hgo : go = gi * doubleCoverVoltage label ar.1 ac := by
            calc
              go = gi * (gi⁻¹ * go) := by simp
              _ = gi * doubleCoverVoltage label ar.1 ac := by rw [hCoeff.1]
          apply Finset.mem_union_left
          apply Finset.mem_map.mpr
          refine ⟨ar, Finset.mem_univ ar, ?_⟩
          subst go
          rfl
      | inr c2 =>
          rcases c2 with ⟨ac', bc, go⟩
          rw [LiftedProduct.boundaryIncidence_checkSupport_inr,
            LiftedProduct.mem_boundary2RowSupport_inl] at hc
          rcases hc with ⟨rfl, hCoeff⟩
          change (LiftedProduct.groupConj
            (doubleCoverTannerMatrix label g' bc br)).coeff (gi * go⁻¹) ≠ 0 at hCoeff
          rw [LiftedProduct.groupConj_apply,
            doubleCoverTannerMatrix_coeff_ne_zero_iff] at hCoeff
          have hgo : go = doubleCoverVoltage label bc.1 br * gi := by
            calc
              go = (go * gi⁻¹) * gi := by simp
              _ = doubleCoverVoltage label bc.1 br * gi := by
                rw [show go * gi⁻¹ = doubleCoverVoltage label bc.1 br by
                  simpa only [mul_inv_rev, inv_inv] using hCoeff.1]
          apply Finset.mem_union_right
          apply Finset.mem_map.mpr
          refine ⟨bc, Finset.mem_univ bc, ?_⟩
          subst go
          rfl
  | inr q =>
      rcases q with ⟨ar, bc, gi⟩
      cases c with
      | inl c0 =>
          rcases c0 with ⟨ar', br, go⟩
          rw [LiftedProduct.boundaryIncidence_checkSupport_inl,
            LiftedProduct.mem_boundary1RowSupport_inr] at hc
          rcases hc with ⟨rfl, hCoeff⟩
          change (LiftedProduct.groupConj
            (doubleCoverTannerMatrix label g' bc br)).coeff (go * gi⁻¹) ≠ 0 at hCoeff
          rw [LiftedProduct.groupConj_apply,
            doubleCoverTannerMatrix_coeff_ne_zero_iff] at hCoeff
          have hgo : go = (doubleCoverVoltage label bc.1 br)⁻¹ * gi := by
            calc
              go = (gi * go⁻¹)⁻¹ * gi := by simp
              _ = (doubleCoverVoltage label bc.1 br)⁻¹ * gi := by
                rw [show gi * go⁻¹ = doubleCoverVoltage label bc.1 br by
                  simpa only [mul_inv_rev, inv_inv] using hCoeff.1]
          apply Finset.mem_union_left
          apply Finset.mem_map.mpr
          refine ⟨br, Finset.mem_univ br, ?_⟩
          subst go
          rfl
      | inr c2 =>
          rcases c2 with ⟨ac, bc', go⟩
          rw [LiftedProduct.boundaryIncidence_checkSupport_inr,
            LiftedProduct.mem_boundary2RowSupport_inr] at hc
          rcases hc with ⟨rfl, hCoeff⟩
          rw [data, doubleCoverTannerMatrix_coeff_ne_zero_iff] at hCoeff
          have hgo : go = gi * (doubleCoverVoltage label ar.1 ac)⁻¹ := by
            calc
              go = gi * (go⁻¹ * gi)⁻¹ := by simp
              _ = gi * (doubleCoverVoltage label ar.1 ac)⁻¹ := by rw [hCoeff.1]
          apply Finset.mem_union_right
          apply Finset.mem_map.mpr
          refine ⟨ac, Finset.mem_univ ac, ?_⟩
          subst go
          rfl
end QEC.Coding.TannerLiftedProduct
