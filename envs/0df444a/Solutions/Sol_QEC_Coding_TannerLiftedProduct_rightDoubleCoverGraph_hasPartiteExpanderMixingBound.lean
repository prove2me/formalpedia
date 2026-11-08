-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_hasPartiteExpanderMixingBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:22:09.571555+00:00
-- url     : https://prove2.me/submissions/dbe0a16d-fee9-4f3a-98fe-ff978730bb37

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_symm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalNeighbor_horizontalNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_eq_card_sideSlice_add
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_crossCount_rightDoubleCoverGraph
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
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
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
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


attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_symm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.horizontalNeighbor_horizontalNeighbor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [DecidableEq W]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (degree : Nat) (spectral : ℝ)
    (hSpectralNonnegative : 0 ≤ spectral)
    (hMixing : SmallSetExpansion.HasExpanderMixingBound
      (rightCayleyGraph label) degree spectral) :
    HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph label) degree spectral := by
  intro S T
  let n : ℝ := Fintype.card G
  let s0 : ℝ := (sideSlice S 0).card
  let s1 : ℝ := (sideSlice S 1).card
  let t0 : ℝ := (sideSlice T 0).card
  let t1 : ℝ := (sideSlice T 1).card
  have hn : 0 ≤ n := by positivity
  have hs0 : 0 ≤ s0 := by positivity
  have hs1 : 0 ≤ s1 := by positivity
  have ht0 : 0 ≤ t0 := by positivity
  have ht1 : 0 ≤ t1 := by positivity
  have hS : (S.card : ℝ) = s0 + s1 := by
    dsimp [s0, s1]
    exact_mod_cast card_eq_card_sideSlice_add S
  have hT : (T.card : ℝ) = t0 + t1 := by
    dsimp [t0, t1]
    exact_mod_cast card_eq_card_sideSlice_add T
  have hCross :
      (SmallSetExpansion.crossCount (rightDoubleCoverGraph label) S T : ℝ) =
        (SmallSetExpansion.crossCount (rightCayleyGraph label)
            (sideSlice S 0) (sideSlice T 1) : ℝ) +
          SmallSetExpansion.crossCount (rightCayleyGraph label)
            (sideSlice T 0) (sideSlice S 1) := by
    exact_mod_cast crossCount_rightDoubleCoverGraph label S T
  have h01 := hMixing (sideSlice S 0) (sideSlice T 1)
  have h10 := hMixing (sideSlice T 0) (sideSlice S 1)
  change n *
      (SmallSetExpansion.crossCount (rightCayleyGraph label)
        (sideSlice S 0) (sideSlice T 1) : ℝ) ≤
      degree * s0 * t1 + spectral * n * Real.sqrt (s0 * t1) at h01
  change n *
      (SmallSetExpansion.crossCount (rightCayleyGraph label)
        (sideSlice T 0) (sideSlice S 1) : ℝ) ≤
      degree * t0 * s1 + spectral * n * Real.sqrt (t0 * s1) at h10
  have hrs0 : (Real.sqrt s0) ^ 2 = s0 := Real.sq_sqrt hs0
  have hrs1 : (Real.sqrt s1) ^ 2 = s1 := Real.sq_sqrt hs1
  have hrt0 : (Real.sqrt t0) ^ 2 = t0 := Real.sq_sqrt ht0
  have hrt1 : (Real.sqrt t1) ^ 2 = t1 := Real.sq_sqrt ht1
  have hCauchySq :
      (Real.sqrt (s0 * t1) + Real.sqrt (t0 * s1)) ^ 2 ≤
        (s0 + s1) * (t0 + t1) := by
    rw [Real.sqrt_mul hs0, Real.sqrt_mul ht0]
    nlinarith [sq_nonneg
      (Real.sqrt s0 * Real.sqrt t0 - Real.sqrt s1 * Real.sqrt t1)]
  have hRootSum :
      Real.sqrt (s0 * t1) + Real.sqrt (t0 * s1) ≤
        Real.sqrt ((s0 + s1) * (t0 + t1)) := by
    have hLeft :
        0 ≤ Real.sqrt (s0 * t1) + Real.sqrt (t0 * s1) := by positivity
    have hProduct : 0 ≤ (s0 + s1) * (t0 + t1) := by positivity
    have hRightSq :
        (Real.sqrt ((s0 + s1) * (t0 + t1))) ^ 2 =
          (s0 + s1) * (t0 + t1) := Real.sq_sqrt hProduct
    have hRight :
        0 ≤ Real.sqrt ((s0 + s1) * (t0 + t1)) := Real.sqrt_nonneg _
    nlinarith
  have hDensity :
      (degree : ℝ) * s0 * t1 + degree * t0 * s1 ≤
        degree * (s0 + s1) * (t0 + t1) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg degree) (mul_nonneg hs0 ht0),
      mul_nonneg (Nat.cast_nonneg degree) (mul_nonneg hs1 ht1)]
  have hSpectral :
      spectral * n *
          (Real.sqrt (s0 * t1) + Real.sqrt (t0 * s1)) ≤
        spectral * n * Real.sqrt ((s0 + s1) * (t0 + t1)) :=
    mul_le_mul_of_nonneg_left hRootSum
      (mul_nonneg hSpectralNonnegative hn)
  rw [hCross, hS, hT]
  nlinarith
end QEC.Coding.TannerLiftedProduct
