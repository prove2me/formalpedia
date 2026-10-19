-- Prove2me | solution 1 for QuantumParallelRepetition.pdfQuantitativeGreedyConditioning
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/a9332990-e5ad-4e26-a012-f970e04a4fbb

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_remainingCoordinates_card
import Theorems.Thm_QuantumParallelRepetition_repeatedStrategy_exists_conditioning
import Theorems.Thm_QuantumParallelRepetition_pdfGreedyCeilingHorizon_le
import Theorems.Thm_QuantumParallelRepetition_pdfGreedyCeilingHorizon_pow_le_exp
import Theorems.Thm_QuantumParallelRepetition_pdfGreedyCard_lt_of_ceil

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (τ d θ : ℝ)
    (_n_positive : 0 < n)
    (threshold : 0 < τ)
    (threshold_lt_one : τ < 1)
    (_rate_positive : 0 < d)
    (rate_small : d ≤ τ / 2)
    (above_exponential : Real.exp (-d * (n : ℝ)) < θ)
    (realized : θ ≤ S.winProbability) :
    ∃ D : Finset (Fin n),
      (D.card : ℝ) < d * (n : ℝ) / τ ∧
      (n : ℝ) / 2 < ((Finset.univ \ D).card : ℝ) ∧
      θ ≤ repeatedPostselectionMass G n S D ∧
      S.winProbability ≤ repeatedPostselectionMass G n S D ∧
      0 < repeatedPostselectionMass G n S D ∧
      0 < (Finset.univ \ D).card ∧
      uniformRemainingFailure
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D < τ := by
  let T : ℕ := ⌈d * (n : ℝ) / τ⌉₊
  have winning : 0 < S.winProbability :=
    lt_of_lt_of_le ((Real.exp_pos _).trans above_exponential) realized
  have legal : T ≤ n :=
    pdfGreedyCeilingHorizon_le n τ d threshold rate_small
  have terminal : (1 - τ) ^ T < S.winProbability :=
    lt_of_le_of_lt
      (pdfGreedyCeilingHorizon_pow_le_exp
        n τ d threshold threshold_lt_one.le)
      (above_exponential.trans_le realized)
  obtain ⟨D, selected, floor, positive, remaining, failure⟩ :=
    repeatedStrategy_exists_conditioning G n S
      winning threshold threshold_lt_one.le legal terminal
  have strict_card : (D.card : ℝ) < d * (n : ℝ) / τ :=
    pdfGreedyCard_lt_of_ceil D.card n τ d selected
  have half_rate : d * (n : ℝ) / τ ≤ (n : ℝ) / 2 := by
    apply (div_le_iff₀ threshold).mpr
    have actual := mul_le_mul_of_nonneg_right rate_small
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  have selected_le : D.card ≤ n := by
    have actual := Finset.card_le_card (Finset.subset_univ D)
    simpa using actual
  have remaining_real :
      ((Finset.univ \ D).card : ℝ) =
        (n : ℝ) - (D.card : ℝ) := by
    rw [remainingCoordinates_card, Nat.cast_sub selected_le]
  have more_than_half :
      (n : ℝ) / 2 < ((Finset.univ \ D).card : ℝ) := by
    rw [remaining_real]
    nlinarith
  exact ⟨D, strict_card, more_than_half,
    realized.trans floor, floor, positive, remaining, failure⟩
end QuantumParallelRepetition
