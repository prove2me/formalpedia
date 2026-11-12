-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P77.weighted_information_security
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:55:30.210301+00:00
-- url     : https://prove2.me/submissions/a3e73981-4c2b-46a7-b944-8c885a999789

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P77

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Intakenext100.P77 in
theorem solution {T : Type} [Fintype T]
    (p : PassWeights T) (info : T → ℝ) (hi : ∀ t, 0 ≤ info t) :
    (∀ a : ℝ, 0 < a →
      luckyProbability p info a * a ≤ ∑ t, p.weight t * info t) ∧
    ∀ (alpha beta : ℝ), 0 < beta → ∀ n : ℕ,
      (∑ t, p.weight t * info t) ≤ Real.exp (2 * (alpha - beta * n)) →
      luckyProbability p info (Real.exp (alpha - beta * n)) ≤
        Real.exp (alpha - beta * n) := by
  have markov : ∀ a : ℝ, 0 < a →
      luckyProbability p info a * a ≤ ∑ t, p.weight t * info t := by
    intro a _
    unfold luckyProbability
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro t _
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left h (p.nonnegative t)
    · rw [zero_mul]
      exact mul_nonneg (p.nonnegative t) (hi t)
  refine ⟨markov, ?_⟩
  intro alpha beta _ n h
  have he : 0 < Real.exp (alpha - beta * n) := Real.exp_pos _
  have h2 : Real.exp (2 * (alpha - beta * n)) =
      Real.exp (alpha - beta * n) * Real.exp (alpha - beta * n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm := markov _ he
  rw [h2] at h
  exact le_of_mul_le_mul_right (hm.trans h) he

end
