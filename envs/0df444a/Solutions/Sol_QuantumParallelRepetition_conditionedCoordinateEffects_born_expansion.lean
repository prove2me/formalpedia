-- Prove2me | solution 1 for QuantumParallelRepetition.conditionedCoordinateEffects_born_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/76220d3b-3b3b-4e58-9560-874baf519bdf

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {j : Fin n // j ∈ D} → A)
    (β : {j : Fin n // j ∈ D} → B)
    (xs : Fin n → X) (ys : Fin n → Y)
    (i : Fin n) (a : A) (b : B) :
    bornTracePairing S.state.matrix
        (conditionedAliceCoordinateEffect G n S D α xs i a)
        (conditionedBobCoordinateEffect G n S D β ys i b) =
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        if (∀ (j : Fin n) (hj : j ∈ D), aa j = α ⟨j, hj⟩) ∧
          aa i = a then
          if (∀ (j : Fin n) (hj : j ∈ D), bb j = β ⟨j, hj⟩) ∧
            bb i = b then S.outcomeProbability xs ys aa bb else 0
        else 0 := by
  classical
  simp only [conditionedAliceCoordinateEffect,
    conditionedBobCoordinateEffect,
    map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro aa _
  split_ifs with ha
  · apply Finset.sum_congr rfl
    intro bb _
    split_ifs with hb
    · rfl
    · exact map_zero _
  · simp
end QuantumParallelRepetition
