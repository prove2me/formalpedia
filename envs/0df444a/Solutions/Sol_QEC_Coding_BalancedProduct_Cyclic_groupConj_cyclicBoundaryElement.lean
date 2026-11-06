-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.Cyclic.groupConj_cyclicBoundaryElement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:31:55.011113+00:00
-- url     : https://prove2.me/submissions/41b8ee63-8e98-49c8-b176-78b46a5d4d61

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicEquiv_apply_eq_generator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicInvEquiv_apply_eq_invGenerator_pow
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
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
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
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


attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.finCyclicEquiv_apply_eq_generator_pow
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.finCyclicInvEquiv_apply_eq_invGenerator_pow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.Cyclic
universe u v
namespace QEC.Coding.BalancedProduct.Cyclic
theorem _root_.solution
    {G : Type u} [Group G] (x : G) :
    LiftedProduct.groupConj (cyclicBoundaryElement x) =
      cyclicBoundaryElement x⁻¹ := by
  classical
  ext g
  have hx : g = x⁻¹ ↔ x = g⁻¹ := by
    constructor
    · intro h
      subst g
      simp
    · intro h
      calc
        g = (g⁻¹)⁻¹ := by simp
        _ = x⁻¹ := by rw [← h]
  rw [LiftedProduct.groupConj_apply]
  unfold cyclicBoundaryElement
  have hadd (a b : MonoidAlgebra (ZMod 2) G) (y : G) :
      (a + b).coeff y = a.coeff y + b.coeff y := rfl
  rw [hadd, hadd]
  change
    (MonoidAlgebra.single 1 1).coeff g⁻¹ + (MonoidAlgebra.single x 1).coeff g⁻¹ =
      (MonoidAlgebra.single 1 1).coeff g + (MonoidAlgebra.single x⁻¹ 1).coeff g
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hOneIff : (1 : G) = g⁻¹ ↔ 1 = g := by
    constructor
    · intro h
      have hg : g = 1 := by
        calc
          g = (g⁻¹)⁻¹ := by simp
          _ = 1 := by rw [← h]; simp
      exact hg.symm
    · intro h
      subst g
      simp
  have hXIff : x = g⁻¹ ↔ x⁻¹ = g := by
    constructor
    · intro h
      exact (hx.mpr h).symm
    · intro h
      exact hx.mp h.symm
  rw [hOneIff, hXIff]
end QEC.Coding.BalancedProduct.Cyclic
