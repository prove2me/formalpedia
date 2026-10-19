-- Prove2me | solution 1 for QuantumParallelRepetition.exact_arbitrarily_large_conditioning_of_subexponentialWitness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/edaa6001-20a5-4d13-940c-e207e953f218

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_uniformRemainingFailure_lt_of_failure_sum
import Theorems.Thm_QuantumParallelRepetition_divisor_greedy_remaining_bounds
import Theorems.Thm_QuantumParallelRepetition_arbitrarily_large_purified_divisor_greedy_conditioning_with_rounding
import Theorems.Thm_QuantumParallelRepetition_exactSourcePinskerRate_le_half_of_martingaleRate

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B)
    (witness : HasSubexponentialWitness (repeatedEntangledValue G))
    {failureTolerance rateTolerance : ℝ}
    (failure_positive : 0 < failureTolerance)
    (failure_at_most_one : failureTolerance ≤ 1)
    (rate_positive : 0 < rateTolerance)
    (lower : ℕ) :
    ∃ n : ℕ, lower < n ∧
      ∃ S : Strategy (G.repeat n),
        ∃ D : Finset (Fin n),
          0 < S.winProbability ∧
          0 < repeatedPostselectionMass G n S D ∧
          0 < (Finset.univ \ D).card ∧
          uniformRemainingFailure
              (strategyEventLaw (G.repeat n) S)
              (repeatedCoordinateWin G n) D < failureTolerance ∧
          martingaleRate G n S D ≤
            rateTolerance ^ 2 / 8 ∧
          exactSourcePinskerRate G n S D ≤
            rateTolerance / 2 := by
  classical
  obtain ⟨q, q_at_least_two, extract⟩ :=
    arbitrarily_large_purified_divisor_greedy_conditioning_with_rounding
      G witness (K := (1 : ℝ))
      failure_positive failure_at_most_one
      (by norm_num) rate_positive
  obtain ⟨n, beyond, S, D, winning, small, mass, failure, cost⟩ :=
    extract lower
  let actual : Strategy (G.repeat n) := purifiedStrategy S
  have actual_positive : 0 < actual.winProbability :=
    lt_trans (Real.exp_pos _) winning
  have postselection_positive :
      0 < repeatedPostselectionMass G n actual D := by
    exact lt_of_lt_of_le actual_positive mass
  have remaining_positive : 0 < (Finset.univ \ D).card :=
    (divisor_greedy_remaining_bounds q_at_least_two small).1
  have failure_small :
      uniformRemainingFailure
          (strategyEventLaw (G.repeat n) actual)
          (repeatedCoordinateWin G n) D < failureTolerance := by
    apply uniformRemainingFailure_lt_of_failure_sum
      (strategyEventLaw (G.repeat n) actual)
      (repeatedCoordinateWin G n) D
      postselection_positive remaining_positive
    exact failure
  have scaled_rate :
      8 * martingaleRate G n actual D ≤ rateTolerance ^ 2 := by
    calc
      8 * martingaleRate G n actual D =
          8 * Real.log
            (fullHistoryAnswerCount (A := A) (B := B) D /
              repeatedPostselectionMass G n actual D) /
            ((Finset.univ \ D).card : ℝ) := by
              unfold martingaleRate
              rw [← martingale_log_cost_eq
                G n actual D postselection_positive]
              ring
      _ ≤ rateTolerance ^ 2 := by
        simpa [actual, repeatedPostselectionMass,
          postselectionMass] using cost
  have actual_rate :
      martingaleRate G n actual D ≤
        rateTolerance ^ 2 / 8 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    nlinarith
  exact ⟨n, beyond, actual, D, actual_positive,
    postselection_positive, remaining_positive, failure_small,
    actual_rate,
    exactSourcePinskerRate_le_half_of_martingaleRate
      G n actual D postselection_positive rate_positive.le actual_rate⟩
end QuantumParallelRepetition
