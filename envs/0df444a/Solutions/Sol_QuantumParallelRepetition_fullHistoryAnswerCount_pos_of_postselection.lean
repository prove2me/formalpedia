-- Prove2me | solution 1 for QuantumParallelRepetition.fullHistoryAnswerCount_pos_of_postselection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/2fc6d0f8-a709-432f-b1cd-03fab91b7bfa

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D)
    (hp : 0 < (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) :
    0 < fullHistoryAnswerCount (A := A) (B := B) D := by
  classical
  have hmass := fullHistoryAtomBornMass_sum G n S D L hL
  have hfirst :
      (∑ t : FullHistoryEntropyAtom X Y A B n D L,
        fullHistoryAtomCountingWeight G D L t *
          fullHistoryAtomBornMass G n S D L t) ≤
        ∑ t : FullHistoryEntropyAtom X Y A B n D L,
          fullHistoryAtomCountingWeight G D L t := by
    apply Finset.sum_le_sum
    intro t _
    exact mul_le_of_le_one_right
      (fullHistoryAtomCountingWeight_nonneg G D L t)
      (fullHistoryAtomBornMass_le_one G n S D L t)
  have hsecond := fullHistoryAtomCountingWeight_sum_le G D L
  linarith
end QuantumParallelRepetition
