-- Prove2me | solution 1 for SeatInventory.Distinct.emsr_optimality_conditions
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T20:33:55.542126+00:00
-- url     : https://prove2.me/submissions/37921b35-a606-477d-85eb-cf8487729001

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

lemma si_emsr_anti (f : ℝ) (hf : 0 ≤ f) (p : PMF ℕ) {a b : ℕ} (h : a ≤ b) :
    emsr f p b ≤ emsr f p a :=
  mul_le_mul_of_nonneg_left (si_tail_antitone p h) hf

lemma si_rev_up (f : ℝ) (hf : 0 ≤ f) (p : PMF ℕ) (a t : ℕ) :
    expectedRevenue f p (a + t) - expectedRevenue f p a ≤ (t : ℝ) * emsr f p (a + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 := si_rev_succ f p (a + t)
    have h2 := si_emsr_anti f hf p (show a + 1 ≤ a + t + 1 by omega)
    rw [show a + (t+1) = a + t + 1 by omega]
    push_cast; linarith

lemma si_rev_down (f : ℝ) (hf : 0 ≤ f) (p : PMF ℕ) (a t : ℕ) :
    (t : ℝ) * emsr f p (a + t) ≤ expectedRevenue f p (a + t) - expectedRevenue f p a := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 := si_rev_succ f p (a + t)
    have h2 := si_emsr_anti f hf p (show a + t ≤ a + t + 1 by omega)
    have h3 : (0:ℝ) ≤ t := by positivity
    rw [show a + (t+1) = a + t + 1 by omega]
    push_cast; nlinarith

theorem emsr_optimality_conditions_core {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (d : ι → PMF ℕ) (C : ℕ) (S : ι → ℕ) (hS : ∑ i, S i = C) :
    (∀ S' : ι → ℕ, ∑ i, S' i = C → totalExpectedRevenue f d S' ≤ totalExpectedRevenue f d S) ↔
      ∃ lam : ℝ, ∀ i, (1 ≤ S i → lam ≤ emsr (f i) (d i) (S i)) ∧
        emsr (f i) (d i) (S i + 1) ≤ lam := by
  classical
  constructor
  · intro hopt
    have key : ∀ i j, 1 ≤ S j → emsr (f i) (d i) (S i + 1) ≤ emsr (f j) (d j) (S j) := by
      intro i j hj
      by_cases hij : i = j
      · subst hij; exact si_emsr_anti _ (hf i) _ (by omega)
      · let S' : ι → ℕ := fun k => S k + (if k = i then 1 else 0) - (if k = j then 1 else 0)
        have hS'C : ∑ k, S' k = C := by
          have hpt : ∀ k, S' k + (if k = j then 1 else 0) = S k + (if k = i then 1 else 0) := by
            intro k
            simp only [S']
            by_cases hki : k = i
            · subst hki; simp [hij]
            · by_cases hkj : k = j
              · subst hkj; simp [hki]; omega
              · simp [hki, hkj]
          have := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hpt k)
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq',
            Finset.sum_ite_eq'] at this
          simp at this; omega
        have hrev : ∀ k, expectedRevenue (f k) (d k) (S' k) - expectedRevenue (f k) (d k) (S k) =
            (if k = i then emsr (f i) (d i) (S i + 1) else 0) -
              (if k = j then emsr (f j) (d j) (S j) else 0) := by
          intro k
          simp only [S']
          by_cases hki : k = i
          · subst hki; simp [hij]; exact si_rev_succ _ _ _
          · by_cases hkj : k = j
            · subst hkj; simp [hki]
              have := si_rev_succ (f k) (d k) (S k - 1)
              rw [show S k - 1 + 1 = S k by omega] at this
              linarith
            · simp [hki, hkj]
        have h := hopt S' hS'C
        unfold totalExpectedRevenue at h
        have hsum : ∑ k, (expectedRevenue (f k) (d k) (S' k) - expectedRevenue (f k) (d k) (S k))
            = emsr (f i) (d i) (S i + 1) - emsr (f j) (d j) (S j) := by
          rw [Finset.sum_congr rfl (fun k _ => hrev k), Finset.sum_sub_distrib,
            Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp
        rw [Finset.sum_sub_distrib] at hsum
        linarith
    by_cases hne : ∃ j, 1 ≤ S j
    · obtain ⟨j0, hj0⟩ := hne
      haveI : Nonempty ι := ⟨j0⟩
      refine ⟨⨆ i, emsr (f i) (d i) (S i + 1), fun i => ⟨fun hi => ?_, ?_⟩⟩
      · exact ciSup_le (fun k => key k i hi)
      · exact le_ciSup (f := fun i => emsr (f i) (d i) (S i + 1)) (Set.finite_range _).bddAbove i
    · push_neg at hne
      refine ⟨⨆ i, emsr (f i) (d i) (S i + 1), fun i => ⟨fun hi => by have := hne i; omega, ?_⟩⟩
      exact le_ciSup (f := fun i => emsr (f i) (d i) (S i + 1)) (Set.finite_range _).bddAbove i
  · rintro ⟨lam, hlam⟩ S' hS'
    have hi : ∀ i, expectedRevenue (f i) (d i) (S' i) - expectedRevenue (f i) (d i) (S i) ≤
        lam * ((S' i : ℝ) - S i) := by
      intro i
      rcases le_or_gt (S i) (S' i) with h | h
      · have := si_rev_up (f i) (hf i) (d i) (S i) (S' i - S i)
        rw [show S i + (S' i - S i) = S' i by omega] at this
        have h2 := (hlam i).2
        have hc : ((S' i - S i : ℕ) : ℝ) = (S' i : ℝ) - S i := by push_cast [h]; ring
        rw [hc] at this
        have h3 : (0:ℝ) ≤ (S' i : ℝ) - S i := by rw [← hc]; positivity
        nlinarith
      · have := si_rev_down (f i) (hf i) (d i) (S' i) (S i - S' i)
        rw [show S' i + (S i - S' i) = S i by omega] at this
        have h2 := (hlam i).1 (by omega)
        have hc : ((S i - S' i : ℕ) : ℝ) = (S i : ℝ) - S' i := by push_cast [h.le]; ring
        rw [hc] at this
        have h3 : (0:ℝ) ≤ (S i : ℝ) - S' i := by rw [← hc]; positivity
        nlinarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
    have e1 : (∑ i, (S' i : ℝ)) = C := by exact_mod_cast hS'
    have e2 : (∑ i, (S i : ℝ)) = C := by exact_mod_cast hS
    unfold totalExpectedRevenue
    rw [e1, e2] at hsum
    linarith

end SeatInventory.Distinct

open SeatInventory.Distinct


theorem solution {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (d : ι → PMF ℕ) (C : ℕ) (S : ι → ℕ) (hS : ∑ i, S i = C) :
    (∀ S' : ι → ℕ, ∑ i, S' i = C → totalExpectedRevenue f d S' ≤ totalExpectedRevenue f d S) ↔
      ∃ lam : ℝ, ∀ i, (1 ≤ S i → lam ≤ emsr (f i) (d i) (S i)) ∧
        emsr (f i) (d i) (S i + 1) ≤ lam := by
  exact emsr_optimality_conditions_core f hf d C S hS
