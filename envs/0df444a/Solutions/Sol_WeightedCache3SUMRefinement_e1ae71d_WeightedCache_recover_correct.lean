-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.WeightedCache.recover_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:06.164245+00:00
-- url     : https://prove2.me/submissions/e02eb05e-3891-41c5-ad36-608dd8d4a74a

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_predecessor_rank_lt

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open WeightedCache3SUMRefinement_e1ae71d.WeightedCache
open Finset
namespace WeightedCache3SUMRefinement_e1ae71d.WeightedCache
theorem _root_.solution {N h : ℕ} (B : Finset (Word N))
    (hbase : ∀ R, rank R ≤ h → R ∈ B) (values F : Word N → ℤ)
    (hbank : ∀ R ∈ B, values R = F R)
    (hF : ∀ R, (∑ i : Fin N, (R i).val * F (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * F R) :
    ∀ k R, rank R ≤ k → recover B values h k R = F R := by
  intro k
  induction k with
  | zero =>
    intro R hR
    exact hbank R (hbase R (by omega))
  | succ k ih =>
    intro R hR
    by_cases hb : R ∈ B
    · simpa [recover, hb] using hbank R hb
    · have hr : h < rank R := by
        by_contra hn
        exact hb (hbase R (by omega))
      simp only [recover, hb, ↓reduceIte]
      have hs : (∑ i : Fin N, (R i).val * recover B values h k (predecessor R i)) =
          ∑ i : Fin N, (R i).val * F (predecessor R i) := by
        apply sum_congr rfl
        intro i _
        by_cases hz : (R i).val = 0
        · simp [hz]
        · rw [ih (predecessor R i)
            (by have ht := predecessor_rank_lt R i (Nat.pos_of_ne_zero hz); omega)]
      rw [hs, hF R]
      exact Int.mul_ediv_cancel_left (F R) (by omega)
end WeightedCache3SUMRefinement_e1ae71d.WeightedCache
