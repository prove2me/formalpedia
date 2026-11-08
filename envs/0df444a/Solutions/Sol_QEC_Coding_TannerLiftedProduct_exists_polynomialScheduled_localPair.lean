-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exists_polynomialScheduled_localPair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:33:39.068873+00:00
-- url     : https://prove2.me/submissions/06b2f0df-88d7-4f5b-91e6-a7b4844464f1

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exactPairFactors_of_blocks
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
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_bidirectional_productExpanding_pair
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coarseRectangleExponent_polynomial_coeff_lt_rank
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
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffaee19b85_24
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffaee19b85_25
omit [DecidableEq R] [DecidableEq R']
set_option maxHeartbeats 1200000
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (A D M S K B B' L n : Nat)
    (hWCard : Fintype.card W = A * n ^ 6)
    (hRCard : Fintype.card R = B * n ^ 6)
    (hR'Card : Fintype.card R' = B' * n ^ 6)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hA : 0 < A) (hDPositive : 0 < D) (hL : 0 < L) (hn : 0 < n)
    (hSmall : 12 * M ≤ D * n ^ 2)
    (hRankTarget : 36 * K * S ≤ 5 * D ^ 2)
    (hFirstKernelBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ B * L ^ (A - D))
    (hFirstImageBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ (A - B) * L ^ (A - D))
    (hSecondKernelBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ B' * L ^ (A - D))
    (hSecondImageBlock :
      6 * (Nat.card F + L) ^ A <
        (Nat.card F) ^ (A - B') * L ^ (A - D))
    (hForwardThreshold :
      2 * A + 2 * A * S + 4 * M * A + 16 * S + 11 < K * B * n)
    (hReverseThreshold :
      2 * A + 2 * A * S + 4 * M * A + 16 * S + 11 < K * B' * n) :
    ∃ (h : Matrix R W F) (h' : Matrix R' W F),
      h.rank = Fintype.card R ∧
      h'.rank = Fintype.card R' ∧
      (∀ c : Word F W, c ∈ (ProductExpansion.parityCheckCode h).carrier →
        c ≠ 0 → D * n ^ 6 ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (ProductExpansion.parityCheckCode
          (ProductExpansion.generatorImageParityCheck h)).carrier →
        c ≠ 0 → D * n ^ 6 ≤ HammingWeight c) ∧
      (∀ c : Word F W, c ∈ (ProductExpansion.parityCheckCode h').carrier →
        c ≠ 0 → D * n ^ 6 ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (ProductExpansion.parityCheckCode
          (ProductExpansion.generatorImageParityCheck h')).carrier →
        c ≠ 0 → D * n ^ 6 ≤ HammingWeight c) ∧
      ProductExpansion.ProductExpanding h
        (ProductExpansion.generatorImageParityCheck h')
        (S * n ^ 7) (2 * (M * n ^ 4))
        (((D * n ^ 6 : Nat) : ℝ) / (3 * (Fintype.card W : ℝ))) ∧
      ProductExpansion.ProductExpanding h'
        (ProductExpansion.generatorImageParityCheck h)
        (S * n ^ 7) (2 * (M * n ^ 4))
        (((D * n ^ 6 : Nat) : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  have hq : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hPair := exactPairFactors_of_blocks
    A D B B' (M * n ^ 4) (S * n ^ 7) (K * n ^ 5)
    (Nat.card F) L (n ^ 6) hD hB hB' hq hL (Nat.pow_pos hn)
    hFirstKernelBlock hFirstImageBlock hSecondKernelBlock hSecondImageBlock
    (coarseRectangleExponent_polynomial_coeff_lt_rank
      A M S K B n (Nat.card F) hq hA hn hForwardThreshold)
    (coarseRectangleExponent_polynomial_coeff_lt_rank
      A M S K B' n (Nat.card F) hq hA hn hReverseThreshold)
  obtain ⟨hFirstKernel, hFirstImage, hSecondKernel, hSecondImage,
      hForwardRectangle, hReverseRectangle⟩ := hPair
  have hPositive : 0 < D * n ^ 6 :=
    Nat.mul_pos hDPositive (Nat.pow_pos hn)
  have hLength : D * n ^ 6 ≤ Fintype.card W := by
    rw [hWCard]
    exact Nat.mul_le_mul_right _ hD
  have hSmallScaled : 6 * (2 * (M * n ^ 4)) ≤ D * n ^ 6 := by
    calc
      6 * (2 * (M * n ^ 4)) = (12 * M) * n ^ 4 := by ring
      _ ≤ (D * n ^ 2) * n ^ 4 := Nat.mul_le_mul_right _ hSmall
      _ = D * n ^ 6 := by ring
  have hRankScaled :
      36 * (K * n ^ 5) * (S * n ^ 7) ≤
        5 * (D * n ^ 6) * (D * n ^ 6) := by
    calc
      36 * (K * n ^ 5) * (S * n ^ 7) =
          (36 * K * S) * n ^ 12 := by ring
      _ ≤ (5 * D ^ 2) * n ^ 12 :=
        Nat.mul_le_mul_right _ hRankTarget
      _ = 5 * (D * n ^ 6) * (D * n ^ 6) := by ring
  apply ProductExpansion.exists_bidirectional_productExpanding_pair
    (F := F) (W := W) (R := R) (R' := R')
    (D * n ^ 6) (S * n ^ 7) (2 * (M * n ^ 4)) (K * n ^ 5)
    hPositive hLength hSmallScaled hRankScaled
  · simpa [hWCard, hRCard] using hFirstKernel
  · simpa [hWCard, hRCard] using hFirstImage
  · simpa [hWCard, hR'Card] using hSecondKernel
  · simpa [hWCard, hR'Card] using hSecondImage
  · simpa [hWCard, hRCard, mul_assoc] using hForwardRectangle
  · simpa [hWCard, hR'Card, mul_assoc] using hReverseRectangle
end QEC.Coding.TannerLiftedProduct
