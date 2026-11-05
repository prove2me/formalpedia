-- Prove2me | solution 2 for QuantumParallelRepetition.pdf_distributionUniformExponential_of_uniform_source_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T05:58:26.985368+00:00
-- url     : https://prove2.me/submissions/5192f579-6ad6-4ef4-91bc-eb2d368f460b

/-
Reorganization of the existing quantum parallel repetition driver.
Supporting proofs adapted from OpenAI's ten-proofs, QuantumParallelRepetition.lean,
commit 94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 (Apache-2.0), as published in
Prove2Me submission f7cea14e-2b4d-4d58-988d-602c87bbeb52.
The two stage boundaries and their composition are the new organization.
-/

import Theorems.Thm_QuantumParallelRepetition_conditioningCertificate_of_above_exponential
import Theorems.Thm_QuantumParallelRepetition_winningStrategy_of_conditioningCertificate
import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_core_26
import Theorems.Thm_QuantumParallelRepetition_winProbabilities_bddAbove

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

noncomputable section

open scoped BigOperators

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exists_repeatedStrategy_of_lt_entangledValue
    (G : Game X Y A B) {n : ℕ} {r : ℝ}
    (hr : 0 < r)
    (hvalue : r < repeatedEntangledValue G n) :
    ∃ S : Strategy (G.repeat n), r < S.winProbability := by
  let values : Set ℝ :=
    Set.range (Strategy.winProbability (G := G.repeat n))
  have hnonempty : values.Nonempty := by
    by_contra hempty
    have heq : values = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    have hzero : repeatedEntangledValue G n = 0 := by
      change sSup values = 0
      rw [heq, Real.sSup_empty]
    linarith
  have hs : r < sSup values := by
    exact hvalue
  obtain ⟨v, ⟨S, hS⟩, hv⟩ := exists_lt_of_lt_csSup hnonempty hs
  subst v
  exact ⟨S, hv⟩

end

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

theorem pdfUniversalRate_pos
    {B : ℝ} (positive : 0 < B) :
    0 < pdfUniversalRate B := by
  unfold pdfUniversalRate
  positivity

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

end QuantumParallelRepetition

open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset


theorem solution
    (rounding :
      ∃ K : ℝ, 1 ≤ K ∧
        ∀ {X Y A B : Type}
          [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
          (G : Game X Y A B)
          (n : ℕ) (S : Strategy (G.repeat n))
          (D : Finset (Fin n)),
          0 < (Finset.univ \ D).card →
          0 < repeatedPostselectionMass G n S D →
          ∀ (alpha gamma : ℝ),
            0 < alpha → alpha ≤ 1 → 0 < gamma →
            uniformRemainingFailure
                (strategyEventLaw (G.repeat n) S)
                (repeatedCoordinateWin G n) D <
              (1 - entangledValue G) / 2 →
            ∃ rounded : Strategy G,
              roundedWinningLowerBound (1 - entangledValue G)
                  K alpha (martingaleRate G n S D)
                  (exactSourcePinskerRate G n S D + gamma) ≤
                rounded.winProbability) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X Y A B : Type}
        [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : Game X Y A B),
        Nonempty A → Nonempty B →
        0 < 1 - entangledValue G →
        ∀ n : ℕ, 0 < n →
          repeatedEntangledValue G n ≤
            Real.exp
              (-(c *
                ((1 - entangledValue G) ^ 13 /
                  ((1 - entangledValue G) +
                    Real.log
                      ((Fintype.card A : ℝ) *
                        (Fintype.card B : ℝ))))) * (n : ℝ)) := by
  obtain ⟨K, constant, round⟩ := rounding
  have coefficient : 1 ≤ pdfRoundingCoefficient K :=
    pdfRoundingCoefficient_one_le constant
  refine ⟨pdfUniversalRate (pdfRoundingCoefficient K),
    pdfUniversalRate_pos (by linarith), ?_⟩
  intro X Y A B _ _ _ _ G alice bob gap n length
  let d : ℝ := pdfGapRate (pdfRoundingCoefficient K) (1 - entangledValue G)
    (Real.log ((Fintype.card A : ℝ) * (Fintype.card B : ℝ)))
  have exponential : repeatedEntangledValue G n ≤ Real.exp (-d * (n : ℝ)) := by
    by_contra not_bound
    obtain ⟨S, winning⟩ :=
      exists_repeatedStrategy_of_lt_entangledValue G (Real.exp_pos _)
        (lt_of_not_ge not_bound)
    -- The conditioning stage supplies exactly the data needed by rounding.
    obtain ⟨D, remaining, positive, failure, entropy, small, pinsker⟩ :=
      conditioningCertificate_of_above_exponential
        G n S K constant alice bob gap length winning
    obtain ⟨rounded, beats_value⟩ :=
      winningStrategy_of_conditioningCertificate G n S D K constant gap
        remaining positive failure entropy small pinsker (round G n S D)
    -- Every legal strategy is bounded by the supremum defining the game value.
    have upper : rounded.winProbability ≤ entangledValue G := by
      unfold entangledValue
      exact le_csSup (winProbabilities_bddAbove G) ⟨rounded, rfl⟩
    exact (not_lt_of_ge upper) beats_value
  simpa [d, pdfGapRate, div_eq_mul_inv, mul_assoc] using exponential
