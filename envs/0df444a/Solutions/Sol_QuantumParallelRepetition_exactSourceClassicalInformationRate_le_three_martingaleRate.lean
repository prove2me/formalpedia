-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceClassicalInformationRate_le_three_martingaleRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/9d2d1d5c-ce28-4243-b34b-3ebd50d12383

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    exactSourceClassicalInformationRate G n S D ≤
      3 * martingaleRate G n S D := by
  have answer_nonnegative :=
    answerLogCost_nonneg_of_postselection
      G n S D positive
  unfold exactSourceClassicalInformationRate
    martingaleRate
  have denominator_nonnegative :
      0 ≤ ((Finset.univ \ D).card : ℝ) := by positivity
  by_cases denominator_zero : ((Finset.univ \ D).card : ℝ) = 0
  · simp [denominator_zero]
  have denominator_positive :
      0 < ((Finset.univ \ D).card : ℝ) :=
    lt_of_le_of_ne denominator_nonnegative (Ne.symm denominator_zero)
  apply (div_le_iff₀ denominator_positive).2
  field_simp
  linarith
end QuantumParallelRepetition
