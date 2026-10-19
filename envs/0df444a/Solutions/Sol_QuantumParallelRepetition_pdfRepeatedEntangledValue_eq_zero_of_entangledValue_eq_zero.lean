-- Prove2me | solution 1 for QuantumParallelRepetition.pdfRepeatedEntangledValue_eq_zero_of_entangledValue_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/42f05d8e-1145-487f-ae42-4c1047356af8

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_entangledValue_eq_zero_of_strategyWinProbability_eq_zero
import Theorems.Thm_QuantumParallelRepetition_pdfPredicate_not_accepted_of_entangledValue_eq_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B)
    (zero : entangledValue G = 0)
    {n : ℕ} (positive : 0 < n) :
    repeatedEntangledValue G n = 0 := by
  classical
  let i : Fin n := ⟨0, positive⟩
  apply entangledValue_eq_zero_of_strategyWinProbability_eq_zero (G.repeat n)
  intro S
  unfold Strategy.winProbability
  apply Finset.sum_eq_zero
  intro xs _
  apply Finset.sum_eq_zero
  intro ys _
  by_cases zero_weight : (G.repeat n).questionWeight xs ys = 0
  · change (G.repeat n).questionWeight xs ys * _ = 0
    rw [zero_weight, zero_mul]
  · have local_nonzero : G.questionWeight (xs i) (ys i) ≠ 0 := by
      intro local_zero
      apply zero_weight
      rw [Game.repeat_questionWeight]
      exact Finset.prod_eq_zero (Finset.mem_univ i) local_zero
    have supported : 0 < G.questionWeight (xs i) (ys i) :=
      lt_of_le_of_ne (G.weight_nonneg (xs i) (ys i)) local_nonzero.symm
    have never (as : Fin n → A) (bs : Fin n → B) :
        (G.repeat n).predicate xs ys as bs ≠ true := by
      intro accepted
      exact pdfPredicate_not_accepted_of_entangledValue_eq_zero
        G zero (xs i) (ys i) (as i) (bs i) supported
        ((Game.repeat_predicate_eq_true G n xs ys as bs).mp accepted i)
    simp [never]
end QuantumParallelRepetition
