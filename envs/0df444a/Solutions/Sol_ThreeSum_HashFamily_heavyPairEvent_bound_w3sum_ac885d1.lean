-- Prove2me | solution 1 for ThreeSum.HashFamily.heavyPairEvent_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:16:58.798389+00:00
-- url     : https://prove2.me/submissions/31a6af2f-8c71-436e-8727-de67175bfa97

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Definitions.Def_WeightedCache3SUM_Alias_eca79955591ab4cf
import Theorems.Thm_ThreeSum_HashFamily_heavyPairEvent_markov
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t : α → Bool} (hst : s ≠ t) (a b : K)
    (vertices : Finset (α → Bool)) (hcross : ∀ u ∈ vertices, u ≠ t)
    (B : ℕ) (hB : 4 * (Fintype.card K + vertices.card) ≤ B * Fintype.card K) :
    4 * Fintype.card K ^ 2 * (heavyPairEvent s t a b vertices B).card ≤
      Fintype.card (α × Bool → K) := by
  have hm := heavyPairEvent_markov s t a b vertices B
  have hl := loadedPairMass_bound hst a b vertices hcross
  have hp : 0 < Fintype.card K := Fintype.card_pos
  have hpos : 0 < B * Fintype.card K := lt_of_lt_of_le (by omega) hB
  apply Nat.le_of_mul_le_mul_left (c := B * Fintype.card K) ?_ hpos
  calc
    _ = 4 * (Fintype.card K ^ 3 *
        (B * (heavyPairEvent s t a b vertices B).card)) := by ring
    _ ≤ 4 * (Fintype.card K ^ 3 * loadedPairMass s t a b vertices) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hm)
    _ ≤ 4 * ((Fintype.card K + vertices.card) * Fintype.card (α × Bool → K)) :=
      Nat.mul_le_mul_left _ hl
    _ ≤ _ := by
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_right (Fintype.card (α × Bool → K)) hB
end ThreeSum.HashFamily
