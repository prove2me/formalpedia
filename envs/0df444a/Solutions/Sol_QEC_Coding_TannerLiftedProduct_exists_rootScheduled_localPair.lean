-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exists_rootScheduled_localPair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:24:47.422793+00:00
-- url     : https://prove2.me/submissions/eef47ffb-dec2-4024-b3b2-6804f1a9d96e

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exactPairFactors_of_rootSchedule
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
    (A D M S K B B' L N x : Nat)
    (hWCard : Fintype.card W = A * N)
    (hRCard : Fintype.card R = B * N)
    (hR'Card : Fintype.card R' = B' * N)
    (hD : D ≤ A) (hB : B ≤ A) (hB' : B' ≤ A)
    (hA : 0 < A) (hDPositive : 0 < D) (hL : 0 < L) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N) (hUpper : N ≤ 64 * x ^ 6)
    (hSmall : 12 * M ≤ D * x ^ 2)
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
      2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11 < K * B * x)
    (hReverseThreshold :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11 < K * B' * x) :
    ∃ (h : Matrix R W F) (h' : Matrix R' W F),
      h.rank = Fintype.card R ∧
      h'.rank = Fintype.card R' ∧
      (∀ c : Word F W, c ∈ (ProductExpansion.parityCheckCode h).carrier →
        c ≠ 0 → D * N ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (ProductExpansion.parityCheckCode
          (ProductExpansion.generatorImageParityCheck h)).carrier →
        c ≠ 0 → D * N ≤ HammingWeight c) ∧
      (∀ c : Word F W, c ∈ (ProductExpansion.parityCheckCode h').carrier →
        c ≠ 0 → D * N ≤ HammingWeight c) ∧
      (∀ c : Word F W,
        c ∈ (ProductExpansion.parityCheckCode
          (ProductExpansion.generatorImageParityCheck h')).carrier →
        c ≠ 0 → D * N ≤ HammingWeight c) ∧
      ProductExpansion.ProductExpanding h
        (ProductExpansion.generatorImageParityCheck h')
        (S * x ^ 7) (2 * (M * x ^ 4))
        (((D * N : Nat) : ℝ) / (3 * (Fintype.card W : ℝ))) ∧
      ProductExpansion.ProductExpanding h'
        (ProductExpansion.generatorImageParityCheck h)
        (S * x ^ 7) (2 * (M * x ^ 4))
        (((D * N : Nat) : ℝ) / (3 * (Fintype.card W : ℝ))) := by
  have hq : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hPair := exactPairFactors_of_rootSchedule
    A D M S K B B' (Nat.card F) L N x
    hD hB hB' hq hA hL hx hLower hUpper
    hFirstKernelBlock hFirstImageBlock hSecondKernelBlock hSecondImageBlock
    hForwardThreshold hReverseThreshold
  obtain ⟨hFirstKernel, hFirstImage, hSecondKernel, hSecondImage,
      hForwardRectangle, hReverseRectangle⟩ := hPair
  have hNPositive : 0 < N := (Nat.pow_pos hx).trans_le hLower
  have hPositive : 0 < D * N := Nat.mul_pos hDPositive hNPositive
  have hLength : D * N ≤ Fintype.card W := by
    rw [hWCard]
    exact Nat.mul_le_mul_right _ hD
  have hSmallScaled : 6 * (2 * (M * x ^ 4)) ≤ D * N := by
    calc
      6 * (2 * (M * x ^ 4)) = (12 * M) * x ^ 4 := by ring
      _ ≤ (D * x ^ 2) * x ^ 4 := Nat.mul_le_mul_right _ hSmall
      _ = D * x ^ 6 := by ring
      _ ≤ D * N := Nat.mul_le_mul_left D hLower
  have hLowerSquare : x ^ 12 ≤ N ^ 2 := by
    calc
      x ^ 12 = (x ^ 6) ^ 2 := by ring
      _ ≤ N ^ 2 := Nat.pow_le_pow_left hLower 2
  have hRankScaled :
      36 * (K * x ^ 5) * (S * x ^ 7) ≤ 5 * (D * N) * (D * N) := by
    calc
      36 * (K * x ^ 5) * (S * x ^ 7) =
          (36 * K * S) * x ^ 12 := by ring
      _ ≤ (5 * D ^ 2) * x ^ 12 :=
        Nat.mul_le_mul_right _ hRankTarget
      _ ≤ (5 * D ^ 2) * N ^ 2 :=
        Nat.mul_le_mul_left (5 * D ^ 2) hLowerSquare
      _ = 5 * (D * N) * (D * N) := by ring
  apply ProductExpansion.exists_bidirectional_productExpanding_pair
    (F := F) (W := W) (R := R) (R' := R')
    (D * N) (S * x ^ 7) (2 * (M * x ^ 4)) (K * x ^ 5)
    hPositive hLength hSmallScaled hRankScaled
  · simpa [hWCard, hRCard] using hFirstKernel
  · simpa [hWCard, hRCard] using hFirstImage
  · simpa [hWCard, hR'Card] using hSecondKernel
  · simpa [hWCard, hR'Card] using hSecondImage
  · simpa [hWCard, hRCard, mul_assoc] using hForwardRectangle
  · simpa [hWCard, hR'Card, mul_assoc] using hReverseRectangle
end QEC.Coding.TannerLiftedProduct
