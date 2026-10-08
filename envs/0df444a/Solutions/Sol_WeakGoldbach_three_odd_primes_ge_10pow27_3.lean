-- Prove2me | solution 3 for WeakGoldbach.three_odd_primes_ge_10pow27
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T21:40:52.913763+00:00
-- url     : https://prove2.me/submissions/7f51aaa1-143b-4ff2-ab6d-e2ab518edba2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Helfgott_etaPlus_abs_le
import Theorems.Thm_Helfgott_etaStar_abs_le
import Theorems.Thm_Helfgott_weighted_count_lower
import Theorems.Thm_Helfgott_three_odd_primes_of_weighted_count

/-! DRAFT TRACKED REDUCTION, not a direct proof of Goldbach.
All four child targets are published. Full proofs of etaStar and extraction
are submitted separately. EtaPlus and the weighted count remain Open obligations.
Written by Codex. -/

open MeasureTheory
open scoped BigOperators

theorem solution (n : ℕ) (hn : 10 ^ 27 ≤ n) (hodd : Odd n) :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  let x : ℝ := (n : ℝ) / (2 + 9 / (196 * Real.sqrt (2 * Real.pi)))
  exact Helfgott.three_odd_primes_of_weighted_count
    (fun m => Helfgott.etaPlus ((m : ℝ) / x))
    (fun m => Helfgott.etaStar ((m : ℝ) / x))
    (fun m => Helfgott.etaPlus_abs_le ((m : ℝ) / x))
    (fun m => Helfgott.etaStar_abs_le ((m : ℝ) / x)) n hn
    (Helfgott.weighted_count_lower n hn hodd)

#print axioms solution
