-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.weightedBlockFactor_lt_of_logarithmicRows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:11:19.935777+00:00
-- url     : https://prove2.me/submissions/39d741c2-e847-4215-88dc-fd3742e29410

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_dualData_A
import Theorems.Thm_QEC_Coding_LiftedProduct_dualData_B
import Theorems.Thm_QEC_Coding_LiftedProduct_dualData_dualData
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_inl_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_inr_apply
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_neg
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_signedSwapWord
import Theorems.Thm_QEC_Coding_LiftedProduct_signedSwapWord_signedUnswapWord
import Theorems.Thm_QEC_Coding_LiftedProduct_signedUnswapWord_signedSwapWord
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalNeighbor_horizontalNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_symm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sq_add_one_pow_le_three_mul
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary1
import Theorems.Thm_QEC_Coding_dualChainComplex_boundary2
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
attribute [local simp] QEC.Coding.LiftedProduct.dualData_A
attribute [local simp] QEC.Coding.LiftedProduct.dualData_B
attribute [local simp] QEC.Coding.LiftedProduct.dualData_dualData
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_inl_apply
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_inr_apply
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_neg
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_signedSwapWord
attribute [local simp] QEC.Coding.LiftedProduct.signedSwapWord_signedUnswapWord
attribute [local simp] QEC.Coding.LiftedProduct.signedUnswapWord_signedSwapWord
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Coding.TannerLiftedProduct.horizontalNeighbor_horizontalNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_symm_apply
attribute [local simp] QEC.Coding.dualChainComplex_boundary1
attribute [local simp] QEC.Coding.dualChainComplex_boundary2
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
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffaee19b85_24
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffaee19b85_25
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q A D r : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hD : D ≤ A)
    (hRows : logarithmicLocalRows q A D ≤ r) :
    6 * (q + quadraticWeightBase q A) ^ A <
      q ^ r * (quadraticWeightBase q A) ^ (A - D) := by
  let e := 2 * D * (Nat.log q A + 1)
  have hqPositive : 0 < q := by omega
  have hAlog : A ≤ q ^ (Nat.log q A + 1) := by
    simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by omega : 1 < q) A).le
  have hAPower : A ^ (2 * D) ≤ q ^ e := by
    calc
      A ^ (2 * D) ≤ (q ^ (Nat.log q A + 1)) ^ (2 * D) :=
        Nat.pow_le_pow_left hAlog _
      _ = q ^ e := by simp [e, ← pow_mul, Nat.mul_comm]
  have hEighteen : 18 < q ^ 5 := by
    calc
      18 < 2 ^ 5 := by norm_num
      _ ≤ q ^ 5 := Nat.pow_le_pow_left hq 5
  have hCore : 18 * A ^ (2 * D) < q ^ (e + 5) := by
    calc
      18 * A ^ (2 * D) ≤ 18 * q ^ e :=
        Nat.mul_le_mul_left 18 hAPower
      _ < q ^ 5 * q ^ e :=
        (Nat.mul_lt_mul_right (Nat.pow_pos hqPositive)).2 hEighteen
      _ = q ^ (e + 5) := by rw [← pow_add, Nat.add_comm]
  have hExponent : D + e + 5 ≤ r := by
    simpa [logarithmicLocalRows, e, Nat.add_assoc] using hRows
  have hSplit : 2 * D + 2 * (A - D) = 2 * A := by omega
  have hSmooth :
      (A ^ 2 + 1) ^ A ≤ 3 * A ^ (2 * A) :=
    sq_add_one_pow_le_three_mul A hA
  have hLeft :
      6 * (q + quadraticWeightBase q A) ^ A ≤
        18 * q ^ A * A ^ (2 * A) := by
    unfold quadraticWeightBase
    calc
      6 * (q + q * A ^ 2) ^ A =
          6 * (q * (A ^ 2 + 1)) ^ A := by ring
      _ = 6 * q ^ A * (A ^ 2 + 1) ^ A := by rw [mul_pow]; ring
      _ ≤ 6 * q ^ A * (3 * A ^ (2 * A)) := by gcongr
      _ = 18 * q ^ A * A ^ (2 * A) := by ring
  have hCoreScaled :
      18 * q ^ A * A ^ (2 * A) <
        q ^ (A + e + 5) * A ^ (2 * (A - D)) := by
    have hPowSplit :
        A ^ (2 * A) = A ^ (2 * D) * A ^ (2 * (A - D)) := by
      rw [← pow_add, hSplit]
    calc
      18 * q ^ A * A ^ (2 * A) =
          q ^ A * (18 * A ^ (2 * D)) * A ^ (2 * (A - D)) := by
        rw [hPowSplit]
        ac_rfl
      _ < q ^ A * q ^ (e + 5) * A ^ (2 * (A - D)) := by
        exact Nat.mul_lt_mul_of_pos_right
          ((Nat.mul_lt_mul_left (Nat.pow_pos hqPositive)).2 hCore)
          (Nat.pow_pos hA)
      _ = q ^ (A + e + 5) * A ^ (2 * (A - D)) := by
        rw [show A + e + 5 = A + (e + 5) by omega]
        simp only [pow_add]
  calc
    6 * (q + quadraticWeightBase q A) ^ A <
        q ^ (A + e + 5) * A ^ (2 * (A - D)) :=
      hLeft.trans_lt hCoreScaled
    _ ≤ q ^ (A + (r - D)) * A ^ (2 * (A - D)) := by
      have hED : e + 5 ≤ r - D := Nat.le_sub_of_add_le (by omega)
      exact Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right hqPositive (by omega))
    _ = q ^ r * (quadraticWeightBase q A) ^ (A - D) := by
      have hDr : D ≤ r := le_trans (Nat.le_add_right D (e + 5)) hExponent
      have hExponentSplit : A + (r - D) = r + (A - D) := by omega
      unfold quadraticWeightBase
      rw [hExponentSplit, pow_add, mul_pow, ← pow_mul]
      ring
end QEC.Coding.TannerLiftedProduct
