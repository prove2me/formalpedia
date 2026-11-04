-- Prove2me | solution 1 for QuantumParallelRepetition.winningStrategy_of_conditioningCertificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T05:58:11.071963+00:00
-- url     : https://prove2.me/submissions/9a20ffbf-4e56-44b2-a8e6-2150fe927ab8

/-
Reorganization of the existing quantum parallel repetition driver.
Supporting proofs adapted from OpenAI's ten-proofs, QuantumParallelRepetition.lean,
commit 94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 (Apache-2.0), as published in
Prove2Me submission f7cea14e-2b4d-4d58-988d-602c87bbeb52.
The two stage boundaries and their composition are the new organization.
-/

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_26
import Theorems.Thm_QuantumParallelRepetition_entangledValue_nonneg

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

noncomputable section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

theorem pdfGapBase_le_gap
    {B ε : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) :
    0 < ε / (4 * B) ∧ ε / (4 * B) ≤ ε := by
  have denominator : 0 < 4 * B := by nlinarith
  constructor
  · exact div_pos gap denominator
  · apply (div_le_iff₀ denominator).2
    nlinarith

theorem pdfGapBase_twelfth_le_gap
    {B ε : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) (unit : ε ≤ 1) :
    (ε / (4 * B)) ^ 12 ≤ ε := by
  obtain ⟨nonnegative, bounded⟩ :=
    pdfGapBase_le_gap constant gap
  calc
    (ε / (4 * B)) ^ 12 ≤ ε ^ 12 :=
      pow_le_pow_left₀ nonnegative.le bounded 12
    _ = ε * ε ^ 11 := by ring
    _ ≤ ε * 1 :=
      mul_le_mul_of_nonneg_left
        (pow_le_one₀ gap.le unit) gap.le
    _ = ε := by ring

theorem pdfGapBase_twelfth_le_one
    {B ε : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε) (unit : ε ≤ 1) :
    (ε / (4 * B)) ^ 12 ≤ 1 :=
  (pdfGapBase_twelfth_le_gap constant gap unit).trans unit

theorem pdfCatalystAccuracy_bounds
    {K ε : ℝ}
    (constant : 1 ≤ K) (gap : 0 < ε) (unit : ε ≤ 1) :
    0 < pdfCatalystAccuracy K ε ∧
      pdfCatalystAccuracy K ε ≤ 1 := by
  have denominator : 0 < 16 * K := by nlinarith
  have ratio : 0 < ε / (16 * K) := div_pos gap denominator
  have bounded : ε / (16 * K) ≤ 1 := by
    apply (div_le_iff₀ denominator).2
    nlinarith
  unfold pdfCatalystAccuracy
  exact ⟨pow_pos ratio 12, pow_le_one₀ ratio.le bounded⟩

theorem pdfCatalystAccuracy_twelfth_root
    {K ε : ℝ} (constant : 1 ≤ K) (gap : 0 < ε) :
    (pdfCatalystAccuracy K ε) ^ (1 / 12 : ℝ) =
      ε / (16 * K) := by
  have denominator : 0 < 16 * K := by nlinarith
  have base : 0 ≤ ε / (16 * K) := (div_pos gap denominator).le
  unfold pdfCatalystAccuracy
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast base (by norm_num : (12 : ℕ) ≠ 0))

theorem pdfGapBase_twelfth_root
    {B ε : ℝ} (constant : 1 ≤ B) (gap : 0 < ε) :
    ((ε / (4 * B)) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) =
      ε / (4 * B) := by
  have base : 0 ≤ ε / (4 * B) :=
    (pdfGapBase_le_gap constant gap).1.le
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast base (by norm_num : (12 : ℕ) ≠ 0))

theorem pdfEntropyRoot_lt_gapBase
    {B ε η : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (entropy : 0 ≤ η)
    (small : η < (ε / (4 * B)) ^ (12 : ℕ)) :
    η ^ (1 / 12 : ℝ) < ε / (4 * B) := by
  calc
    η ^ (1 / 12 : ℝ) <
        ((ε / (4 * B)) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) :=
      Real.rpow_lt_rpow entropy small (by norm_num)
    _ = ε / (4 * B) :=
      pdfGapBase_twelfth_root constant gap

theorem pdfEntropyRoundingLoss_lt_gapQuarter
    {B ε η : ℝ}
    (constant : 1 ≤ B) (gap : 0 < ε)
    (entropy : 0 ≤ η)
    (small : η < (ε / (4 * B)) ^ (12 : ℕ)) :
    B * η ^ (1 / 12 : ℝ) < ε / 4 := by
  have coefficient : 0 < B := by linarith
  calc
    B * η ^ (1 / 12 : ℝ) < B * (ε / (4 * B)) :=
      mul_lt_mul_of_pos_left
        (pdfEntropyRoot_lt_gapBase constant gap entropy small)
        coefficient
    _ = ε / 4 := by
      field_simp

theorem pdfCatalystAccuracy_samplingLoss
    {K ε : ℝ} (constant : 1 ≤ K) (gap : 0 < ε) :
    2 * K * (pdfCatalystAccuracy K ε) ^ (1 / 12 : ℝ) =
      ε / 8 := by
  have coefficient : 0 < K := by linarith
  rw [pdfCatalystAccuracy_twelfth_root constant gap]
  field_simp
  norm_num

end

noncomputable section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem pdfUniversalErrorCeiling_pos
    {K : ℝ} (constant : 1 ≤ K) :
    0 < universalErrorCeiling K := by
  have nonnegative : 0 ≤ K := by linarith
  unfold universalErrorCeiling
  positivity

theorem pdfRoundingCoefficient_two_le
    {K : ℝ} (constant : 1 ≤ K) :
    2 ≤ pdfRoundingCoefficient K := by
  have nonnegative : 0 ≤ K := by linarith
  have ceiling_nonnegative : 0 ≤ universalErrorCeiling K :=
    (pdfUniversalErrorCeiling_pos constant).le
  have first_nonnegative :
      0 ≤ (5 + 2 * universalErrorCeiling K) *
        Real.sqrt (3 / 2 : ℝ) := by positivity
  have quantum_nonnegative :
      0 ≤ 2 * K * (32 : ℝ) ^ (1 / 12 : ℝ) := by positivity
  have eight : 1 ≤ Real.sqrt (8 : ℝ) :=
    Real.one_le_sqrt.mpr (by norm_num)
  unfold pdfRoundingCoefficient
  nlinarith

theorem pdfRoundingCoefficient_one_le
    {K : ℝ} (constant : 1 ≤ K) :
    1 ≤ pdfRoundingCoefficient K := by
  have lower := pdfRoundingCoefficient_two_le constant
  linarith

end

noncomputable section

theorem pdfSqrt_le_twelfthRoot
    {eta : ℝ} (nonnegative : 0 ≤ eta) (bounded : eta ≤ 1) :
    Real.sqrt eta ≤ eta ^ (1 / 12 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge'
    nonnegative bounded (by norm_num) (by norm_num)

theorem pdfPinskerRoot_le_twelfthRoot
    {eta kappa : ℝ}
    (nonnegative : 0 ≤ eta)
    (bounded : eta ≤ 1)
    (pinsker : kappa ≤ Real.sqrt ((3 / 2 : ℝ) * eta)) :
    kappa ≤ Real.sqrt (3 / 2 : ℝ) * eta ^ (1 / 12 : ℝ) := by
  calc
    kappa ≤ Real.sqrt ((3 / 2 : ℝ) * eta) := pinsker
    _ = Real.sqrt (3 / 2 : ℝ) * Real.sqrt eta := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    _ ≤ Real.sqrt (3 / 2 : ℝ) * eta ^ (1 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (pdfSqrt_le_twelfthRoot nonnegative bounded)
        (Real.sqrt_nonneg _)

theorem pdfSqrtEight_le_twelfthRoot
    {eta : ℝ} (nonnegative : 0 ≤ eta) (bounded : eta ≤ 1) :
    Real.sqrt (8 * eta) ≤
      Real.sqrt (8 : ℝ) * eta ^ (1 / 12 : ℝ) := by
  calc
    Real.sqrt (8 * eta) =
        Real.sqrt (8 : ℝ) * Real.sqrt eta := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    _ ≤ Real.sqrt (8 : ℝ) * eta ^ (1 / 12 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (pdfSqrt_le_twelfthRoot nonnegative bounded)
        (Real.sqrt_nonneg _)

theorem pdfQuantitativeRoundingLoss
    {K alpha eta kappa gamma : ℝ}
    (constant : 0 ≤ K)
    (nonnegative : 0 ≤ eta)
    (bounded : eta ≤ 1)
    (pinsker : kappa ≤ Real.sqrt ((3 / 2 : ℝ) * eta)) :
    totalSamplingLoss K alpha eta (kappa + gamma) ≤
      2 * K * alpha ^ (1 / 12 : ℝ) +
        pdfRoundingCoefficient K * eta ^ (1 / 12 : ℝ) +
        (5 + 2 * universalErrorCeiling K) * gamma := by
  have ceiling : 0 ≤ universalErrorCeiling K := by
    unfold universalErrorCeiling
    positivity
  have classical_coefficient :
      0 ≤ 5 + 2 * universalErrorCeiling K := by
    nlinarith
  have pinsker_bound :=
    pdfPinskerRoot_le_twelfthRoot nonnegative bounded pinsker
  have weighted_pinsker :
      (5 + 2 * universalErrorCeiling K) * kappa ≤
        (5 + 2 * universalErrorCeiling K) *
          (Real.sqrt (3 / 2 : ℝ) * eta ^ (1 / 12 : ℝ)) :=
    mul_le_mul_of_nonneg_left pinsker_bound classical_coefficient
  have sqrt_bound :=
    pdfSqrtEight_le_twelfthRoot nonnegative bounded
  have weighted_sqrt :
      2 * Real.sqrt (8 * eta) ≤
        2 * (Real.sqrt (8 : ℝ) * eta ^ (1 / 12 : ℝ)) :=
    mul_le_mul_of_nonneg_left sqrt_bound (by norm_num)
  have source_bounds := add_le_add weighted_pinsker weighted_sqrt
  calc
    totalSamplingLoss K alpha eta (kappa + gamma) =
        2 * K * alpha ^ (1 / 12 : ℝ) +
          ((5 + 2 * universalErrorCeiling K) * kappa +
            2 * Real.sqrt (8 * eta)) +
          2 * K *
            ((32 : ℝ) ^ (1 / 12 : ℝ) * eta ^ (1 / 12 : ℝ)) +
          (5 + 2 * universalErrorCeiling K) * gamma := by
      unfold totalSamplingLoss
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) nonnegative]
      ring
    _ ≤ 2 * K * alpha ^ (1 / 12 : ℝ) +
          ((5 + 2 * universalErrorCeiling K) *
              (Real.sqrt (3 / 2 : ℝ) * eta ^ (1 / 12 : ℝ)) +
            2 * (Real.sqrt (8 : ℝ) * eta ^ (1 / 12 : ℝ))) +
          2 * K *
            ((32 : ℝ) ^ (1 / 12 : ℝ) * eta ^ (1 / 12 : ℝ)) +
          (5 + 2 * universalErrorCeiling K) * gamma := by
      gcongr
    _ = 2 * K * alpha ^ (1 / 12 : ℝ) +
          pdfRoundingCoefficient K * eta ^ (1 / 12 : ℝ) +
          (5 + 2 * universalErrorCeiling K) * gamma := by
      unfold pdfRoundingCoefficient
      ring

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

noncomputable section

theorem pdfGap_le_one
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) :
    1 - entangledValue G ≤ 1 := by
  have nonnegative := entangledValue_nonneg G
  linarith

theorem pdfFullQuantitativeSamplingLoss
    {K ε eta kappa : ℝ}
    (constant : 1 ≤ K)
    (gap : 0 < ε)
    (unit : ε ≤ 1)
    (entropy : 0 ≤ eta)
    (small :
      eta <
        (ε / (4 * pdfRoundingCoefficient K)) ^ (12 : ℕ))
    (pinsker : kappa ≤ Real.sqrt ((3 / 2 : ℝ) * eta)) :
    totalSamplingLoss K (pdfCatalystAccuracy K ε) eta
      (kappa + ε / (16 * (5 + 2 * universalErrorCeiling K))) <
        ε / 2 := by
  have coefficient : 1 ≤ pdfRoundingCoefficient K :=
    pdfRoundingCoefficient_one_le constant
  have bounded : eta ≤ 1 :=
    small.le.trans
      (pdfGapBase_twelfth_le_one coefficient gap unit)
  have loss := pdfQuantitativeRoundingLoss
    (K := K) (alpha := pdfCatalystAccuracy K ε)
    (eta := eta) (kappa := kappa)
    (gamma := ε / (16 * (5 + 2 * universalErrorCeiling K)))
    (by linarith) entropy bounded pinsker
  have entropy_loss :
      pdfRoundingCoefficient K * eta ^ (1 / 12 : ℝ) <
        ε / 4 :=
    pdfEntropyRoundingLoss_lt_gapQuarter
      coefficient gap entropy small
  have catalyst_loss :
      2 * K *
        (pdfCatalystAccuracy K ε) ^ (1 / 12 : ℝ) =
        ε / 8 :=
    pdfCatalystAccuracy_samplingLoss constant gap
  have ceiling : 0 < universalErrorCeiling K :=
    pdfUniversalErrorCeiling_pos constant
  have gamma_loss :
      (5 + 2 * universalErrorCeiling K) *
          (ε / (16 * (5 + 2 * universalErrorCeiling K))) =
        ε / 16 := by
    field_simp
  linarith

end

end QuantumParallelRepetition

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset


theorem solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (K : ℝ) (constant : 1 ≤ K)
    (gap : 0 < 1 - entangledValue G)
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (failure :
      uniformRemainingFailure (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D < (1 - entangledValue G) / 2)
    (entropy : 0 ≤ martingaleRate G n S D)
    (small :
      martingaleRate G n S D <
        ((1 - entangledValue G) / (4 * pdfRoundingCoefficient K)) ^ (12 : ℕ))
    (pinsker :
      exactSourcePinskerRate G n S D ≤
        Real.sqrt ((3 / 2 : ℝ) * martingaleRate G n S D))
    (round :
      0 < (Finset.univ \ D).card →
      0 < repeatedPostselectionMass G n S D →
      ∀ (alpha gamma : ℝ),
        0 < alpha → alpha ≤ 1 → 0 < gamma →
        uniformRemainingFailure (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D < (1 - entangledValue G) / 2 →
        ∃ rounded : Strategy G,
          roundedWinningLowerBound (1 - entangledValue G) K alpha
            (martingaleRate G n S D) (exactSourcePinskerRate G n S D + gamma) ≤
            rounded.winProbability) :
    ∃ rounded : Strategy G, entangledValue G < rounded.winProbability := by
  let ε : ℝ := 1 - entangledValue G
  let alpha : ℝ := pdfCatalystAccuracy K ε
  let gamma : ℝ := ε / (16 * (5 + 2 * universalErrorCeiling K))
  have unit : ε ≤ 1 := pdfGap_le_one G
  have alpha_bounds := pdfCatalystAccuracy_bounds constant gap unit
  have ceiling : 0 < universalErrorCeiling K := pdfUniversalErrorCeiling_pos constant
  have gamma_positive : 0 < gamma := by
    dsimp [gamma]
    positivity
  obtain ⟨rounded, rounded_bound⟩ :=
    round remaining positive alpha gamma alpha_bounds.1 alpha_bounds.2
      gamma_positive failure
  have actual_loss : totalSamplingLoss K alpha (martingaleRate G n S D)
      (exactSourcePinskerRate G n S D + gamma) < ε / 2 :=
    pdfFullQuantitativeSamplingLoss constant gap unit entropy small pinsker
  refine ⟨rounded, ?_⟩
  unfold roundedWinningLowerBound at rounded_bound
  dsimp [ε] at actual_loss
  linarith
