-- Prove2me | solution 1 for WeightedCache.euler_unique_from_downset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:27:28.905813+00:00
-- url     : https://prove2.me/submissions/ef9775b6-51cc-4c0c-aef9-d6804ece3aba

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
import Definitions.Def_Submission_Weighted_Cache
import Theorems.Thm_WeightedCache_predecessor_rank_lt

set_option autoImplicit false
open WeightedCache
open Finset
namespace WeightedCache
theorem _root_.solution {N h : ℕ} (B : Finset (Word N))
    (hbase : ∀ R, rank R ≤ h → R ∈ B) (F G : Word N → ℤ)
    (hF : ∀ R, (∑ i : Fin N, (R i).val * F (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * F R)
    (hG : ∀ R, (∑ i : Fin N, (R i).val * G (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * G R)
    (hbank : ∀ R ∈ B, F R = G R) : F = G := by
  funext R
  have hall : ∀ k, ∀ R : Word N, rank R = k → F R = G R := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro R hR
      by_cases hb : R ∈ B
      · exact hbank R hb
      · have hr : h < rank R := by
          by_contra hn
          exact hb (hbase R (by omega))
        have hs : (∑ i : Fin N, (R i).val * F (predecessor R i)) =
            ∑ i : Fin N, (R i).val * G (predecessor R i) := by
          apply sum_congr rfl
          intro i _
          by_cases hz : (R i).val = 0
          · simp [hz]
          · rw [ih (rank (predecessor R i))
                (by have ht := predecessor_rank_lt R i (Nat.pos_of_ne_zero hz); omega)
                (predecessor R i) rfl]
        rw [hF R, hG R] at hs
        exact mul_left_cancel₀ (by omega : (rank R : ℤ) - (h : ℤ) ≠ 0) hs
  exact hall (rank R) R rfl
end WeightedCache
