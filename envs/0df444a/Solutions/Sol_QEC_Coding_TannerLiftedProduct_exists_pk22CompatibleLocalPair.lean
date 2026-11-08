-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exists_pk22CompatibleLocalPair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:29:01.588021+00:00
-- url     : https://prove2.me/submissions/e726fa69-52e1-47f4-847d-f4ffb214f3bd

import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Definitions.Def_QEC_Coding_ExpanderCodes_CompatibleLocalPair
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_CompatibleDegreePrime_blocks_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_CompatibleDegreePrime_degree_eq_block_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_compatibleDegreePrime_nthRoot_ge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_pk22ParameterIndex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_rootScheduled_localPair
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalNeighbor_horizontalNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_le_sixtyFour_mul_nthRoot_six_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22DistanceCoefficient_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22LocalWidth_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22ParameterBase_pos
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22_blockWitnesses
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22_rankCoefficient_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22_rateCoefficient_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22_scale_bounds
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_replicatedSchedule_rateRatio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_symm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_two_mul_sqrt_compatibleDegreePrime_le_pk22SpectralScale
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
variable {F : Type}
attribute [local instance] QEC.Coding.TannerLiftedProduct.pk22LocalPairDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (F : Type) [Field F] [Fintype F]
    (rate : ℝ) (hRate : rate < 1) :
    ∃ (t : Nat)
      (a : CompatibleDegreePrime (pk22LocalWidth (Nat.card F) t))
      (h h' : Matrix (PK22Check (Nat.card F) t a)
        (PK22Direction (Nat.card F) t a) F),
      pk22ScaleThreshold (Nat.card F) t ≤ Nat.nthRoot 6 a.blocks ∧
      pk22DistanceCoefficient (Nat.card F) t * a.blocks ≤
        Fintype.card (PK22Direction (Nat.card F) t a) ∧
      h.rank = Fintype.card (PK22Check (Nat.card F) t a) ∧
      h'.rank = Fintype.card (PK22Check (Nat.card F) t a) ∧
      (∀ c : Word F (PK22Direction (Nat.card F) t a),
        c ∈ (ProductExpansion.parityCheckCode h).carrier → c ≠ 0 →
        pk22DistanceCoefficient (Nat.card F) t * a.blocks ≤
          HammingWeight c) ∧
      (∀ c : Word F (PK22Direction (Nat.card F) t a),
        c ∈ (ProductExpansion.parityCheckCode h').carrier → c ≠ 0 →
        pk22DistanceCoefficient (Nat.card F) t * a.blocks ≤
          HammingWeight c) ∧
      ProductExpansion.ProductExpanding h
        (ProductExpansion.generatorImageParityCheck h')
        (pk22FaceCoefficient (Nat.card F) t *
          (Nat.nthRoot 6 a.blocks) ^ 7)
        (2 * (Nat.nthRoot 6 a.blocks) ^ 4)
        (((pk22DistanceCoefficient (Nat.card F) t * a.blocks : Nat) : ℝ) /
          (3 * (Fintype.card (PK22Direction (Nat.card F) t a) : ℝ))) ∧
      ProductExpansion.ProductExpanding h'
        (ProductExpansion.generatorImageParityCheck h)
        (pk22FaceCoefficient (Nat.card F) t *
          (Nat.nthRoot 6 a.blocks) ^ 7)
        (2 * (Nat.nthRoot 6 a.blocks) ^ 4)
        (((pk22DistanceCoefficient (Nat.card F) t * a.blocks : Nat) : ℝ) /
          (3 * (Fintype.card (PK22Direction (Nat.card F) t a) : ℝ))) ∧
      2 * ((Fintype.card (PK22Check (Nat.card F) t a) : ℝ) +
          Fintype.card (PK22Check (Nat.card F) t a)) *
          Fintype.card (PK22Direction (Nat.card F) t a) ≤
        (1 - rate) *
          ((Fintype.card (PK22Direction (Nat.card F) t a) : ℝ) ^ 2 +
            4 * Fintype.card (PK22Check (Nat.card F) t a) *
              Fintype.card (PK22Check (Nat.card F) t a)) ∧
      2 * Real.sqrt (a.p : ℝ) ≤
        ((pk22SpectralCoefficient (Nat.card F) t *
          (Nat.nthRoot 6 a.blocks) ^ 3 : Nat) : ℝ) := by
  let q := Nat.card F
  have hq : 2 ≤ q := by
    dsimp [q]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  obtain ⟨t, hRowsLarge, hDistanceLarge, hRateLarge⟩ :=
    exists_pk22ParameterIndex q hq rate hRate
  let A := pk22LocalWidth q t
  let D := pk22DistanceCoefficient q t
  let B := pk22RowCoefficient q t
  let C := pk22SpectralCoefficient q t
  let S := pk22FaceCoefficient q t
  have hAPositive : 0 < A := by
    dsimp [A, pk22LocalWidth]
    exact Nat.pow_pos (pk22ParameterBase_pos q t)
  have hAOdd : Odd A := by
    simpa [A] using pk22LocalWidth_odd q t
  obtain ⟨a, hScale⟩ :=
    exists_compatibleDegreePrime_nthRoot_ge
      A (pk22ScaleThreshold q t) hAPositive hAOdd
  let N := a.blocks
  let x := Nat.nthRoot 6 N
  have hNPositive : 0 < N := by
    exact a.blocks_pos hAPositive
  have hxLower : x ^ 6 ≤ N := by
    exact Nat.pow_nthRoot_le (by norm_num)
  have hxUpper : N ≤ 64 * x ^ 6 :=
    le_sixtyFour_mul_nthRoot_six_pow N hNPositive
  have hScale' : pk22ScaleThreshold q t ≤ x := by
    simpa [A, N, x] using hScale
  obtain ⟨hxPositive, hSmall, hBudgetCoefficient, hRectangleScale,
      hVertical, hEdge, hFace, hRectangleThreshold⟩ :=
    pk22_scale_bounds q t x hScale'
  obtain ⟨hDLe, hBLe, hLPositive, hFirstKernel, hFirstImage,
      hSecondKernel, hSecondImage⟩ :=
    pk22_blockWitnesses q t hq hRowsLarge hDistanceLarge
  have hRankCoefficient : 36 * 1 * S ≤ 5 * D ^ 2 := by
    simpa [S, D] using pk22_rankCoefficient_bound q t
  have hWCard : Fintype.card (PK22Direction q t a) = A * N := by
    simpa [PK22Direction, A, N] using a.degree_eq_block_mul
  have hRCard : Fintype.card (PK22Check q t a) = B * N := by
    simp [PK22Check, B, N]
  have hRectangleThreshold' :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * 1 * (64 * A) +
          16 * S + 11 < 1 * B * x := by
    simpa [pk22RectangleConstant, A, B, S] using hRectangleThreshold
  obtain ⟨h, h', hRank, h'Rank, hDistance, _hImageDistance,
      hDistanceReverse, _hImageDistanceReverse,
      hProductExpand, hProductExpandReverse⟩ :=
    exists_rootScheduled_localPair
      (F := F) (W := PK22Direction q t a)
      (R := PK22Check q t a) (R' := PK22Check q t a)
      A D 1 S 1 B B (quadraticWeightBase q A) N x
      hWCard hRCard hRCard
      (by simpa [D, A] using hDLe)
      (by simpa [B, A] using hBLe)
      (by simpa [B, A] using hBLe)
      hAPositive (by simpa [D] using pk22DistanceCoefficient_pos q t)
      (by simpa [A] using hLPositive) hxPositive hxLower hxUpper
      (by simpa [D] using hSmall) hRankCoefficient
      (by simpa only [A, D, B] using hFirstKernel)
      (by simpa only [A, D, B] using hFirstImage)
      (by simpa only [A, D, B] using hSecondKernel)
      (by simpa only [A, D, B] using hSecondImage)
      hRectangleThreshold' hRectangleThreshold'
  have hRateCoefficient :=
    pk22_rateCoefficient_bound q t hq rate hRate hRateLarge
  have hRateRatio :=
    replicatedSchedule_rateRatio A B B N rate (by
      simpa [A, B] using hRateCoefficient)
  have hSpectralScale :=
    two_mul_sqrt_compatibleDegreePrime_le_pk22SpectralScale q t x a hxUpper
  have hLength : D * N ≤ Fintype.card (PK22Direction q t a) := by
    rw [hWCard]
    exact Nat.mul_le_mul_right N hDLe
  refine ⟨t, a, h, h', ?_, ?_, hRank, h'Rank, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [q, N, x] using hScale'
  · simpa [q, D, N] using hLength
  · simpa [q, D, N] using hDistance
  · simpa [q, D, N] using hDistanceReverse
  · simpa [q, D, S, N, x] using hProductExpand
  · simpa [q, D, S, N, x] using hProductExpandReverse
  · simpa [q, A, B, N, hWCard, hRCard] using hRateRatio
  · simpa [q, N, x] using hSpectralScale
end QEC.Coding.TannerLiftedProduct
