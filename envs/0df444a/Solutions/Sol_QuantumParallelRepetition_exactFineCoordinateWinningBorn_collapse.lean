-- Prove2me | solution 1 for QuantumParallelRepetition.exactFineCoordinateWinningBorn_collapse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/1fc49102-0852-4d30-b165-f7060c61a784

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_conditionedCoordinateEffects_born_expansion

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (xs : Fin n → X) (ys : Fin n → Y)
    (coordinate : Fin n) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B,
      if G.predicate x y a b = true then
        bornTracePairing S.state.matrix
          (conditionedAliceCoordinateEffect
            G n S D aliceAnswer xs coordinate a)
          (conditionedBobCoordinateEffect
            G n S D bobAnswer ys coordinate b)
      else 0) =
    ∑ aa : Fin n → A, ∑ bb : Fin n → B,
      if
        (∀ (j : Fin n) (member : j ∈ D),
          aa j = aliceAnswer ⟨j, member⟩) ∧
        (∀ (j : Fin n) (member : j ∈ D),
          bb j = bobAnswer ⟨j, member⟩) ∧
        G.predicate x y (aa coordinate) (bb coordinate) = true
      then S.outcomeProbability xs ys aa bb
      else 0 := by
  classical
  simp_rw [conditionedCoordinateEffects_born_expansion G n S D]
  let f : A → B → (Fin n → A) → (Fin n → B) → ℝ :=
    fun a b aa bb =>
      if G.predicate x y a b = true then
        if
          (∀ (j : Fin n) (member : j ∈ D),
            aa j = aliceAnswer ⟨j, member⟩) ∧ aa coordinate = a
        then
          if
            (∀ (j : Fin n) (member : j ∈ D),
              bb j = bobAnswer ⟨j, member⟩) ∧ bb coordinate = b
          then S.outcomeProbability xs ys aa bb
          else 0
        else 0
      else 0
  calc
    (∑ a : A, ∑ b : B,
      if G.predicate x y a b = true then
        ∑ aa : Fin n → A, ∑ bb : Fin n → B,
          if
            (∀ (j : Fin n) (member : j ∈ D),
              aa j = aliceAnswer ⟨j, member⟩) ∧ aa coordinate = a
          then
            if
              (∀ (j : Fin n) (member : j ∈ D),
                bb j = bobAnswer ⟨j, member⟩) ∧ bb coordinate = b
            then S.outcomeProbability xs ys aa bb
            else 0
          else 0
      else 0) =
      ∑ a : A, ∑ b : B,
        ∑ aa : Fin n → A, ∑ bb : Fin n → B, f a b aa bb := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          by_cases wins : G.predicate x y a b = true
          · simp [f, wins]
          · simp [f, wins]
    _ = ∑ aa : Fin n → A, ∑ bb : Fin n → B,
      ∑ a : A, ∑ b : B, f a b aa bb :=
        finite_sum_four_swap f
    _ = ∑ aa : Fin n → A, ∑ bb : Fin n → B,
      if
        (∀ (j : Fin n) (member : j ∈ D),
          aa j = aliceAnswer ⟨j, member⟩) ∧
        (∀ (j : Fin n) (member : j ∈ D),
          bb j = bobAnswer ⟨j, member⟩) ∧
        G.predicate x y (aa coordinate) (bb coordinate) = true
      then S.outcomeProbability xs ys aa bb
      else 0 := by
        apply Finset.sum_congr rfl
        intro aa _
        apply Finset.sum_congr rfl
        intro bb _
        by_cases alice_matches :
          ∀ (j : Fin n) (member : j ∈ D),
            aa j = aliceAnswer ⟨j, member⟩
        · by_cases bob_matches :
            ∀ (j : Fin n) (member : j ∈ D),
              bb j = bobAnswer ⟨j, member⟩
          · rw [Finset.sum_eq_single (aa coordinate)]
            · rw [Finset.sum_eq_single (bb coordinate)]
              · dsimp only [f]
                by_cases wins :
                  G.predicate x y (aa coordinate) (bb coordinate) = true
                · rw [if_pos wins,
                    if_pos ⟨alice_matches, rfl⟩,
                    if_pos ⟨bob_matches, rfl⟩,
                    if_pos ⟨alice_matches, bob_matches, wins⟩]
                · rw [if_neg wins,
                    if_neg (fun h => wins h.2.2)]
              · intro b _ different
                simp [f, Ne.symm different]
              · simp
            · intro a _ different
              simp [f, Ne.symm different]
            · simp
          · simp [f, bob_matches]
        · simp [f, alice_matches]
end QuantumParallelRepetition
