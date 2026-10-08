-- Prove2me | solution 1 for SeatInventory.Distinct.emsr_marginal_revenue
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:13:29.676925+00:00
-- url     : https://prove2.me/submissions/d0b8524b-a02c-4654-be4e-8e131b3dc556

import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel

open SeatInventory.Distinct in
lemma c4134946_summ (p : PMF ℕ) (S : ℕ) :
    Summable (fun r : ℕ => (p r).toReal * ((min r S : ℕ) : ℝ)) := by
  have hs : Summable (fun r : ℕ => (p r).toReal) := ENNReal.summable_toReal (by simp [PMF.tsum_coe])
  refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_) (hs.mul_right (S : ℝ))
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right r S) ENNReal.toReal_nonneg

open SeatInventory.Distinct in
theorem solution (f : ℝ) (p : PMF ℕ) (S : ℕ) :
    expectedRevenue f p (S + 1) - expectedRevenue f p S = emsr f p (S + 1) := by
  unfold expectedRevenue emsr expectedBookings tailProb
  rw [← mul_sub, ← (c4134946_summ p (S+1)).tsum_sub (c4134946_summ p S),
    PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq]
  · congr 1
    refine tsum_congr (fun r => ?_)
    rw [← mul_sub]
    by_cases h : S + 1 ≤ r
    · rw [Set.indicator_of_mem (Set.mem_Ici.mpr h)]
      rw [min_eq_right h, min_eq_right (by omega)]
      push_cast; ring
    · rw [Set.indicator_of_notMem (by simpa using h)]
      rw [min_eq_left (by omega), min_eq_left (by omega)]
      simp
  · intro r
    exact ne_top_of_le_ne_top (PMF.apply_ne_top p r) (Set.indicator_le_self _ _ r)
