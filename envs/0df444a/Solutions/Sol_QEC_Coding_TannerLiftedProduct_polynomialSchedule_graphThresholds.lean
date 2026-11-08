-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.polynomialSchedule_graphThresholds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:33:13.826198+00:00
-- url     : https://prove2.me/submissions/3cfdaf1a-dd1e-4356-971f-4a8486ca0594

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_log_mul_self_pow_le_add
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
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_24
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (A D M S C n : Nat) (lambda : ℝ) (hn : 0 < n)
    (hLambdaNonnegative : 0 ≤ lambda)
    (hLambda : lambda ≤ ((C * n ^ 3 : Nat) : ℝ))
    (hVertical : 2 * M + C ≤ D * n ^ 2)
    (hEdge : 4 * C ≤ M * n)
    (hFace : 16 * (2 * A + 6 * n + 1) * C ^ 2 ≤ S * n) :
    ((2 * (M * n ^ 4) : Nat) : ℝ) + lambda ≤ (D * n ^ 6 : Nat) ∧
    2 * (2 * lambda) ≤ ((M * n ^ 4 : Nat) : ℝ) ∧
    2 * (((Nat.log 2 (2 * (A * n ^ 6)) + 1 : Nat) : ℝ) *
      (8 * lambda ^ 2)) ≤ ((S * n ^ 7 : Nat) : ℝ) := by
  have hN3N4 : n ^ 3 ≤ n ^ 4 :=
    Nat.pow_le_pow_right hn (by norm_num)
  have hVerticalNat :
      2 * (M * n ^ 4) + C * n ^ 3 ≤ D * n ^ 6 := by
    calc
      2 * (M * n ^ 4) + C * n ^ 3 ≤
          2 * (M * n ^ 4) + C * n ^ 4 := by
        gcongr
      _ = (2 * M + C) * n ^ 4 := by ring
      _ ≤ (D * n ^ 2) * n ^ 4 := Nat.mul_le_mul_right _ hVertical
      _ = D * n ^ 6 := by ring
  have hVerticalReal :
      ((2 * (M * n ^ 4) : Nat) : ℝ) + ((C * n ^ 3 : Nat) : ℝ) ≤
        (D * n ^ 6 : Nat) := by
    exact_mod_cast hVerticalNat
  have hEdgeNat : 4 * (C * n ^ 3) ≤ M * n ^ 4 := by
    calc
      4 * (C * n ^ 3) = (4 * C) * n ^ 3 := by ring
      _ ≤ (M * n) * n ^ 3 := Nat.mul_le_mul_right _ hEdge
      _ = M * n ^ 4 := by ring
  have hEdgeReal :
      4 * ((C * n ^ 3 : Nat) : ℝ) ≤ (M * n ^ 4 : Nat) := by
    exact_mod_cast hEdgeNat
  have hLog : Nat.log 2 (2 * (A * n ^ 6)) + 1 ≤
      2 * A + 6 * n + 1 := by
    have hBase : Nat.log 2 (2 * (A * n ^ 6)) ≤ 2 * A + n * 6 := by
      simpa [mul_assoc] using
        (log_mul_self_pow_le_add 2 (2 * A) n 6 (by norm_num))
    omega
  have hLambdaSquare : lambda ^ 2 ≤
      (((C * n ^ 3 : Nat) : ℝ) ^ 2) := by
    exact (sq_le_sq₀ hLambdaNonnegative (by positivity)).2 hLambda
  have hFaceNat :
      16 * (2 * A + 6 * n + 1) * C ^ 2 * n ^ 6 ≤ S * n ^ 7 := by
    calc
      16 * (2 * A + 6 * n + 1) * C ^ 2 * n ^ 6 ≤
          (S * n) * n ^ 6 := Nat.mul_le_mul_right _ hFace
      _ = S * n ^ 7 := by ring
  have hFaceReal :
      16 * ((2 * A + 6 * n + 1 : Nat) : ℝ) *
          (((C * n ^ 3 : Nat) : ℝ) ^ 2) ≤
        ((S * n ^ 7 : Nat) : ℝ) := by
    have hFaceNat' :
        16 * (2 * A + 6 * n + 1) * (C * n ^ 3) ^ 2 ≤ S * n ^ 7 := by
      calc
        16 * (2 * A + 6 * n + 1) * (C * n ^ 3) ^ 2 =
            16 * (2 * A + 6 * n + 1) * C ^ 2 * n ^ 6 := by ring
        _ ≤ S * n ^ 7 := hFaceNat
    exact_mod_cast hFaceNat'
  constructor
  · linarith
  constructor
  · linarith
  · calc
      2 * (((Nat.log 2 (2 * (A * n ^ 6)) + 1 : Nat) : ℝ) *
          (8 * lambda ^ 2)) =
          16 * ((Nat.log 2 (2 * (A * n ^ 6)) + 1 : Nat) : ℝ) *
            lambda ^ 2 := by ring
      _ ≤ 16 * ((2 * A + 6 * n + 1 : Nat) : ℝ) *
          (((C * n ^ 3 : Nat) : ℝ) ^ 2) := by
        gcongr
      _ ≤ ((S * n ^ 7 : Nat) : ℝ) := hFaceReal
end QEC.Coding.TannerLiftedProduct
