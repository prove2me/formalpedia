-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LiftedProductDuality.boundary1_dualData_swapWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:38:25.077667+00:00
-- url     : https://prove2.me/submissions/ac2acd47-0234-4a91-a50e-38fb3edf0ec6

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inl_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_inr_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_swapWord_swapWord
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_A
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_B
import Theorems.Thm_QEC_Coding_BalancedProduct_LiftedProductDuality_dualData_dualData
import Theorems.Thm_P2M_QEC_Coding_wordLinearMapTranspose_toLin__apply_6aba8976cbc7
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicEquiv_apply_eq_generator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_finCyclicInvEquiv_apply_eq_invGenerator_pow
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_A
import Theorems.Thm_QEC_Coding_BalancedProduct_Cyclic_liftedProductData_B_apply
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
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
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.finCyclicEquiv_apply_eq_generator_pow
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.finCyclicInvEquiv_apply_eq_invGenerator_pow
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.liftedProductData_A
attribute [local simp] QEC.Coding.BalancedProduct.Cyclic.liftedProductData_B_apply
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
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


attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inl_apply
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_inr_apply
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.swapWord_swapWord
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_A
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_B
attribute [local simp] QEC.Coding.BalancedProduct.LiftedProductDuality.dualData_dualData

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LiftedProductDuality
open QEC.Coding
universe u v
namespace QEC.Coding.BalancedProduct.LiftedProductDuality
theorem _root_.solution
    {G aRow aCol bRow bCol : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : LiftedProduct.Data (ZMod 2) G aRow aCol bRow bCol)
    (z : Word (ZMod 2)
      (LiftedProduct.QubitIndex aRow aCol bRow bCol G)) :
    LiftedProduct.boundary1 (dualData D) (swapWord z) =
      wordLinearMapTranspose (LiftedProduct.boundary2 D) z := by
  funext p
  rcases p with ⟨ac, bc, go⟩
  rw [LiftedProduct.boundary1, LiftedProduct.boundary2,
    wordLinearMapTranspose_toLin'_apply]
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fintype.sum_prod_type,
    LiftedProduct.boundary1Matrix_inl_apply,
    LiftedProduct.boundary1Matrix_inr_apply_zmod2,
    LiftedProduct.boundary2Matrix_inl_apply,
    LiftedProduct.boundary2Matrix_inr_apply,
    dualData_A, dualData_B, swapWord_inl_apply, swapWord_inr_apply]
  have hleft (a : MonoidAlgebra (ZMod 2) G) (g h : G) :
      LiftedProduct.leftRegularMatrix (LiftedProduct.groupConj a) g h =
        LiftedProduct.leftRegularMatrix a h g := by
    exact (congrFun (congrFun
      (LiftedProduct.leftRegularMatrix_groupConj_transpose a) g) h).symm
  have hright (a : MonoidAlgebra (ZMod 2) G) (g h : G) :
      LiftedProduct.rightRegularMatrix (LiftedProduct.groupConj a) g h =
        LiftedProduct.rightRegularMatrix a h g := by
    exact (congrFun (congrFun
      (LiftedProduct.rightRegularMatrix_groupConj_transpose a) g) h).symm
  conv_rhs => rw [add_comm]
  congr 1
  · apply Fintype.sum_congr
    intro ar
    apply Fintype.sum_congr
    intro br
    apply Fintype.sum_congr
    intro gi
    by_cases hbr : bc = br
    · subst br
      simp only [if_pos, LiftedProduct.starTranspose_apply, hright, mul_comm]
    · have hbr' : br ≠ bc := fun h => hbr h.symm
      simp only [if_neg hbr, if_neg hbr', mul_zero, zero_mul]
  · apply Fintype.sum_congr
    intro ac'
    apply Fintype.sum_congr
    intro br
    apply Fintype.sum_congr
    intro gi
    by_cases hac : ac = ac'
    · subst ac'
      simp only [if_pos, LiftedProduct.starTranspose_apply, hleft, mul_comm]
    · have hac' : ac' ≠ ac := fun h => hac h.symm
      simp only [if_neg hac, if_neg hac', mul_zero, zero_mul]
end QEC.Coding.BalancedProduct.LiftedProductDuality
