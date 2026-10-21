-- Prove2me | solution 3 for WeakGoldbach.three_odd_primes_10pow27_to_exp3100
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T14:48:35.838163+00:00
-- url     : https://prove2.me/submissions/270d0c4f-9be9-4aef-bd88-e40b9cbd345e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Helfgott_weighted_count_lower
import Theorems.Thm_Helfgott_three_odd_primes_of_weighted_count
import Theorems.Thm_Helfgott_etaPlus_abs_le
import Theorems.Thm_Helfgott_etaStar_abs_le

open MeasureTheory
open scoped BigOperators

theorem solution (n : ℕ) (hlo : 10 ^ 27 ≤ n) (hhi : (n : ℝ) < Real.exp 3100) (hodd : Odd n) :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  have hcount := Helfgott.weighted_count_lower n hlo hodd
  exact Helfgott.three_odd_primes_of_weighted_count _ _
    (fun k => Helfgott.etaPlus_abs_le _) (fun k => Helfgott.etaStar_abs_le _) n hlo hcount
