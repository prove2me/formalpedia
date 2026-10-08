-- Prove2me | solution 1 for SeatInventory.Distinct.bookings_add_spill
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T20:32:45.843814+00:00
-- url     : https://prove2.me/submissions/83894765-4679-4b14-96c6-6c3e29e7a8cc

import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel



namespace SeatInventory.Distinct

lemma si_summable_q (p : PMF ℕ) : Summable (fun r : ℕ => (p r).toReal) :=
  ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)

lemma si_tail_eq (p : PMF ℕ) (k : ℕ) :
    tailProb p k = ∑' r : ℕ, (if k ≤ r then (p r).toReal else 0) := by
  unfold tailProb
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq]
  · congr 1; ext r
    by_cases h : k ≤ r
    · simp [h]
    · simp [h]
  · intro r
    exact ne_top_of_le_ne_top (PMF.apply_ne_top p r) (Set.indicator_le_self _ _ r)

lemma si_tail_nonneg (p : PMF ℕ) (k : ℕ) : 0 ≤ tailProb p k := ENNReal.toReal_nonneg

lemma si_tail_anti (p : PMF ℕ) (k : ℕ) : tailProb p (k+1) ≤ tailProb p k := by
  unfold tailProb
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← p.tsum_coe]
    exact ENNReal.tsum_le_tsum (fun r => Set.indicator_le_self _ _ r)
  · apply MeasureTheory.OuterMeasureClass.measure_mono
    intro x hx; simp only [Set.mem_Ici] at *; omega

lemma si_tail_antitone (p : PMF ℕ) : Antitone (tailProb p) :=
  antitone_nat_of_succ_le (si_tail_anti p)

lemma si_bookings_succ (p : PMF ℕ) (S : ℕ) :
    expectedBookings p (S+1) = expectedBookings p S + tailProb p (S+1) := by
  rw [si_tail_eq]
  unfold expectedBookings
  have hq := si_summable_q p
  have h1 : Summable (fun r : ℕ => (p r).toReal * ((min r S : ℕ) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_) (hq.mul_right (S:ℝ))
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    exact_mod_cast Nat.min_le_right r S
  have h2 : Summable (fun r : ℕ => (if S+1 ≤ r then (p r).toReal else 0)) := by
    refine Summable.of_nonneg_of_le (fun r => by split_ifs <;> positivity) (fun r => ?_) hq
    split_ifs <;> simp
  rw [← h1.tsum_add h2]
  congr 1; ext r
  by_cases h : S + 1 ≤ r
  · rw [if_pos h, show min r (S+1) = min r S + 1 by omega]; push_cast; ring
  · rw [if_neg h, show min r (S+1) = min r S by omega]; ring

lemma si_bookings_zero (p : PMF ℕ) : expectedBookings p 0 = 0 := by
  simp [expectedBookings]

lemma si_rev_succ (f : ℝ) (p : PMF ℕ) (S : ℕ) :
    expectedRevenue f p (S + 1) - expectedRevenue f p S = emsr f p (S + 1) := by
  unfold expectedRevenue emsr; rw [si_bookings_succ]; ring

theorem emsr_marginal_revenue_core (f : ℝ) (p : PMF ℕ) (S : ℕ) :
    expectedRevenue f p (S + 1) - expectedRevenue f p S = emsr f p (S + 1) := si_rev_succ f p S

theorem bookings_add_spill_core (p : PMF ℕ) (hmean : Summable (fun r : ℕ => (p r).toReal * (r : ℝ)))
    (S : ℕ) :
    expectedBookings p S + expectedSpill p S = meanRequests p := by
  unfold expectedBookings expectedSpill meanRequests
  have hq := si_summable_q p
  have h1 : Summable (fun r : ℕ => (p r).toReal * ((min r S : ℕ) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_) (hq.mul_right (S:ℝ))
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    exact_mod_cast Nat.min_le_right r S
  have h2 : Summable (fun r : ℕ => (p r).toReal * ((r - S : ℕ) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_) hmean
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    exact_mod_cast Nat.sub_le r S
  rw [← h1.tsum_add h2]
  congr 1; ext r
  rw [← mul_add]; congr 1
  rw [← Nat.cast_add, show min r S + (r - S) = r by omega]

end SeatInventory.Distinct

open SeatInventory.Distinct


theorem solution (p : PMF ℕ) (hmean : Summable (fun r : ℕ => (p r).toReal * (r : ℝ)))
    (S : ℕ) :
    expectedBookings p S + expectedSpill p S = meanRequests p := by
  exact bookings_add_spill_core p hmean S
