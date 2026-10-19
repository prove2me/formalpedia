-- Prove2me | solution 1 for QuantumParallelRepetition.fullHistoryAnswerCount_le_sourceAnswerAlphabetBound_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/5a955046-177d-4443-b405-5d907c25e698

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
    {n : ℕ} (D : Finset (Fin n)) :
    fullHistoryAnswerCount (A := A) (B := B) D ≤
      sourceAnswerAlphabetBound A B ^ D.card := by
  rw [fullHistoryAnswerCount_eq, ← mul_pow]
  exact pow_le_pow_left₀
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (le_max_right 1 _) _
end QuantumParallelRepetition
