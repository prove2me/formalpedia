-- Prove2me | solution 1 for QuantumParallelRepetition.strategyEventLaw_winEvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/171cf6a6-0535-43c9-9048-a5ffa512bf43

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (S : Strategy G) :
    (strategyEventLaw G S).eventMass (strategyWinEvent G) =
      S.winProbability := by
  classical
  unfold FiniteEventLaw.eventMass strategyWinEvent
  simp only [Finset.sum_filter]
  change
    (∑ ω : X × Y × A × B,
      if G.predicate ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = true
      then G.questionWeight ω.1 ω.2.1 *
        S.outcomeProbability ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
      else 0) =
      S.winProbability
  simp_rw [Fintype.sum_prod_type]
  unfold Strategy.winProbability
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  split <;> simp
end QuantumParallelRepetition
