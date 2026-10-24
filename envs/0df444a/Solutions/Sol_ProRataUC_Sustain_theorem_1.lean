-- Prove2me | solution 1 for ProRataUC.Sustain.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T16:40:53.876281+00:00
-- url     : https://prove2.me/submissions/a2ea287d-e2d6-4b82-a8cb-bb2ed99fc49b

import Mathlib
import Definitions.Def_ProRataUC_Sustain_Setting

set_option autoImplicit false

namespace ProRataUC.Sustain.P4627

open ProRataUC.Sustain

lemma solo_eq {M : Type*} (s : Setting M) (j : M) (hq1 : 0 < s.q1) (hq1' : s.q1 ≤ 1)
    (hq2 : 0 < s.q2) (hq2' : s.q2 ≤ 1) (hx : 0 ≤ s.lam1 * s.pi1 j) (hy : 0 ≤ s.lam2 * s.pi2 j) :
    soloRevenue s j = max (min (s.lam1 * s.pi1 j) (s.lam2 * s.pi2 j))
      (max (s.q1 * (s.lam1 * s.pi1 j)) (s.q2 * (s.lam2 * s.pi2 j))) := by
  have hub : ∀ r, r * demand s j r ≤ max (min (s.lam1 * s.pi1 j) (s.lam2 * s.pi2 j))
      (max (s.q1 * (s.lam1 * s.pi1 j)) (s.q2 * (s.lam2 * s.pi2 j))) := by
    intro r
    unfold demand
    split_ifs with h1 h2 h3
    · rw [mul_zero]
      exact le_max_of_le_left (le_min hx hy)
    · exact le_max_of_le_right (le_max_of_le_left (by nlinarith [h2.1]))
    · exact le_max_of_le_right (le_max_of_le_right (by nlinarith [h3.2]))
    · have hrx : r ≤ s.lam1 * s.pi1 j := by
        by_contra hc
        push_neg at hc
        exact h1 ⟨hc, not_le.mp (fun hy' => h3 ⟨hc, hy'⟩)⟩
      have hry : r ≤ s.lam2 * s.pi2 j := by
        by_contra hc
        push_neg at hc
        exact h2 ⟨hrx, hc⟩
      rw [mul_one]
      exact le_max_of_le_left (le_min hrx hry)
  have hbdd : BddAbove (Set.range fun r => r * demand s j r) := by
    exact ⟨_, Set.forall_mem_range.2 hub⟩
  apply le_antisymm (ciSup_le hub)
  apply max_le
  · refine le_ciSup_of_le hbdd (min (s.lam1 * s.pi1 j) (s.lam2 * s.pi2 j)) ?_
    have m1 := min_le_left (s.lam1 * s.pi1 j) (s.lam2 * s.pi2 j)
    have m2 := min_le_right (s.lam1 * s.pi1 j) (s.lam2 * s.pi2 j)
    unfold demand
    split_ifs with h1 h2 h3
    · exact absurd h1.1 (not_lt.2 m1)
    · exact absurd h2.2 (not_lt.2 m2)
    · exact absurd h3.1 (not_lt.2 m1)
    · rw [mul_one]
  · apply max_le
    · refine le_ciSup_of_le hbdd (s.lam1 * s.pi1 j) ?_
      unfold demand
      split_ifs with h1 h2 h3
      · exact absurd h1.1 (lt_irrefl _)
      · rw [mul_comm]
      · exact absurd h3.1 (lt_irrefl _)
      · nlinarith
    · refine le_ciSup_of_le hbdd (s.lam2 * s.pi2 j) ?_
      unfold demand
      split_ifs with h1 h2 h3
      · exact absurd h1.2 (lt_irrefl _)
      · exact absurd h2.2 (lt_irrefl _)
      · rw [mul_comm]
      · nlinarith

lemma key_pr (l1 l2 q1 q2 a b : ℝ) (hl1 : 0 < l1) (hl12 : l1 < l2) (hq1 : 0 < q1) (hq2 : 0 < q2)
    (hq : q1 + q2 = 1) (ha : 0 < a) (hb : 0 ≤ b) :
    max (min (l1 * a) (l2 * b)) (max (q1 * (l1 * a)) (q2 * (l2 * b))) ≤
        l1 * (q1 * l1 * a + q2 * l2 * b) / (q1 * l1 + q2 * l2) ↔
      b / a ∈ Set.Icc (q1 * (l2 - l1) / l2) (q1 * l1 ^ 2 / (l2 ^ 2 * q2 + l1 * l2 * (q1 - q2))) ∪
        Set.Icc 1 (q1 * l1 ^ 2 / (l2 * q2 ^ 2 * (l2 - l1))) := by
  obtain ⟨t, rfl⟩ : ∃ t, b = t * a := ⟨b / a, (div_mul_cancel₀ b ha.ne').symm⟩
  rw [mul_div_cancel_right₀ t ha.ne']
  have hl2 : 0 < l2 := by linarith
  have hd : 0 < l2 - l1 := by linarith
  obtain rfl : q1 = 1 - q2 := by linarith
  have hD : 0 < (1 - q2) * l1 + q2 * l2 := by
    have := mul_pos hq1 hl1
    have := mul_pos hq2 hl2
    linarith
  have hDn1 : 0 < l2 ^ 2 * q2 + l1 * l2 * (1 - q2 - q2) := by
    have := mul_pos hl2 (add_pos (mul_pos hq1 hl1) (mul_pos hq2 hd))
    nlinarith
  have hDn2 : 0 < l2 * q2 ^ 2 * (l2 - l1) := by positivity
  have e1 : l1 * a ≤ l1 * ((1 - q2) * l1 * a + q2 * l2 * (t * a)) / ((1 - q2) * l1 + q2 * l2) ↔
      1 ≤ t := by
    have k : l1 * ((1 - q2) * l1 * a + q2 * l2 * (t * a)) / ((1 - q2) * l1 + q2 * l2) - l1 * a =
        (l1 * a * q2 * l2 / ((1 - q2) * l1 + q2 * l2)) * (t - 1) := by
      field_simp
      ring
    rw [← sub_nonneg, k, mul_nonneg_iff_of_pos_left (div_pos (by positivity) hD), sub_nonneg]
  have e2 : l2 * (t * a) ≤ l1 * ((1 - q2) * l1 * a + q2 * l2 * (t * a)) / ((1 - q2) * l1 + q2 * l2) ↔
      t ≤ (1 - q2) * l1 ^ 2 / (l2 ^ 2 * q2 + l1 * l2 * (1 - q2 - q2)) := by
    have k : l1 * ((1 - q2) * l1 * a + q2 * l2 * (t * a)) / ((1 - q2) * l1 + q2 * l2) - l2 * (t * a) =
        (a / ((1 - q2) * l1 + q2 * l2)) *
          ((1 - q2) * l1 ^ 2 - t * (l2 ^ 2 * q2 + l1 * l2 * (1 - q2 - q2))) := by
      field_simp
      ring
    conv_rhs => rw [le_div_iff₀ hDn1]
    rw [← sub_nonneg, k, mul_nonneg_iff_of_pos_left (div_pos ha hD), sub_nonneg]
  have e3 : (1 - q2) * (l1 * a) ≤
      l1 * ((1 - q2) * l1 * a + q2 * l2 * (t * a)) / ((1 - q2) * l1 + q2 * l2) ↔
      (1 - q2) * (l2 - l1) / l2 ≤ t := by
    have k : l1 * ((1 - q2) * l1 * a + q2 * l2 * (t * a)) / ((1 - q2) * l1 + q2 * l2) -
        (1 - q2) * (l1 * a) =
        (a * l1 * q2 * l2 / ((1 - q2) * l1 + q2 * l2)) * (t - (1 - q2) * (l2 - l1) / l2) := by
      field_simp
      ring
    rw [← sub_nonneg, k, mul_nonneg_iff_of_pos_left (div_pos (by positivity) hD), sub_nonneg]
  have e4 : q2 * (l2 * (t * a)) ≤
      l1 * ((1 - q2) * l1 * a + q2 * l2 * (t * a)) / ((1 - q2) * l1 + q2 * l2) ↔
      t ≤ (1 - q2) * l1 ^ 2 / (l2 * q2 ^ 2 * (l2 - l1)) := by
    have k : l1 * ((1 - q2) * l1 * a + q2 * l2 * (t * a)) / ((1 - q2) * l1 + q2 * l2) -
        q2 * (l2 * (t * a)) =
        (a * (l2 * q2 ^ 2 * (l2 - l1)) / ((1 - q2) * l1 + q2 * l2)) *
          ((1 - q2) * l1 ^ 2 / (l2 * q2 ^ 2 * (l2 - l1)) - t) := by
      field_simp
      ring
    rw [← sub_nonneg, k, mul_nonneg_iff_of_pos_left (div_pos (mul_pos ha hDn2) hD), sub_nonneg]
  have hU : (1 - q2) * l1 ^ 2 / (l2 ^ 2 * q2 + l1 * l2 * (1 - q2 - q2)) ≤
      (1 - q2) * l1 ^ 2 / (l2 * q2 ^ 2 * (l2 - l1)) := by
    apply div_le_div_of_nonneg_left (by positivity) hDn2
    have := mul_pos (mul_pos hl2 hq1) (add_pos hl1 (mul_pos hq2 hd))
    nlinarith
  have hL : (1 - q2) * (l2 - l1) / l2 ≤ 1 := by
    rw [div_le_one hl2]
    nlinarith [mul_pos hq2 hd]
  rw [max_le_iff, max_le_iff, min_le_iff, e1, e2, e3, e4]
  simp only [Set.mem_union, Set.mem_Icc]
  constructor
  · rintro ⟨h1 | h1, hL', hU2⟩
    · exact Or.inr ⟨h1, hU2⟩
    · exact Or.inl ⟨hL', h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Or.inr h2, h1, h2.trans hU⟩
    · exact ⟨Or.inl h1, hL.trans h1, h2⟩

lemma key_uc (l1 l2 q1 q2 a b : ℝ) (hl1 : 0 < l1) (hl12 : l1 < l2) (hq1 : 0 < q1) (hq2 : 0 < q2)
    (hq : q1 + q2 = 1) (ha : 0 < a) (hb : 0 ≤ b) :
    max (min (l1 * a) (l2 * b)) (max (q1 * (l1 * a)) (q2 * (l2 * b))) ≤
        l1 * (q1 * a + q2 * b) ↔
      b / a ∈ Set.Icc 0 (q1 * l1 / (l2 - q2 * l1)) ∪ Set.Icc 1 (q1 * l1 / (q2 * (l2 - l1))) := by
  obtain ⟨t, rfl⟩ : ∃ t, b = t * a := ⟨b / a, (div_mul_cancel₀ b ha.ne').symm⟩
  rw [mul_div_cancel_right₀ t ha.ne']
  have ht : 0 ≤ t := (mul_nonneg_iff_of_pos_right ha).mp hb
  have hl2 : 0 < l2 := by linarith
  have hd : 0 < l2 - l1 := by linarith
  obtain rfl : q1 = 1 - q2 := by linarith
  have hA : 0 < l2 - q2 * l1 := by nlinarith
  have hB : 0 < q2 * (l2 - l1) := by positivity
  have e1 : l1 * a ≤ l1 * ((1 - q2) * a + q2 * (t * a)) ↔ 1 ≤ t := by
    have k : l1 * ((1 - q2) * a + q2 * (t * a)) - l1 * a = (l1 * a * q2) * (t - 1) := by ring
    rw [← sub_nonneg, k, mul_nonneg_iff_of_pos_left (by positivity), sub_nonneg]
  have e2 : l2 * (t * a) ≤ l1 * ((1 - q2) * a + q2 * (t * a)) ↔
      t ≤ (1 - q2) * l1 / (l2 - q2 * l1) := by
    have k : l1 * ((1 - q2) * a + q2 * (t * a)) - l2 * (t * a) =
        a * ((1 - q2) * l1 - t * (l2 - q2 * l1)) := by
      ring
    conv_rhs => rw [le_div_iff₀ hA]
    rw [← sub_nonneg, k, mul_nonneg_iff_of_pos_left ha, sub_nonneg]
  have e3 : (1 - q2) * (l1 * a) ≤ l1 * ((1 - q2) * a + q2 * (t * a)) := by
    have : 0 ≤ l1 * q2 * t * a := by positivity
    nlinarith
  have e4 : q2 * (l2 * (t * a)) ≤ l1 * ((1 - q2) * a + q2 * (t * a)) ↔
      t ≤ (1 - q2) * l1 / (q2 * (l2 - l1)) := by
    have k : l1 * ((1 - q2) * a + q2 * (t * a)) - q2 * (l2 * (t * a)) =
        (a * (q2 * (l2 - l1))) * ((1 - q2) * l1 / (q2 * (l2 - l1)) - t) := by
      field_simp
      ring
    rw [← sub_nonneg, k, mul_nonneg_iff_of_pos_left (mul_pos ha hB), sub_nonneg]
  have hAB : (1 - q2) * l1 / (l2 - q2 * l1) ≤ (1 - q2) * l1 / (q2 * (l2 - l1)) := by
    apply div_le_div_of_nonneg_left (by positivity) hB
    nlinarith
  rw [max_le_iff, max_le_iff, min_le_iff, e1, e2, e4, iff_true_intro e3, true_and]
  simp only [Set.mem_union, Set.mem_Icc]
  constructor
  · rintro ⟨h1 | h1, hB2⟩
    · exact Or.inr ⟨h1, hB2⟩
    · exact Or.inl ⟨ht, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Or.inr h2, h2.trans hAB⟩
    · exact ⟨Or.inl h1, h2⟩

end ProRataUC.Sustain.P4627

open ProRataUC.Sustain in
theorem solution {M : Type*} [Fintype M] (s : Setting M) (hs : s.Standing) (hA : Assumption1 s)
    (hpos : ∀ j, 0 < s.pi1 j) :
    (SustainablePR s ↔ ∀ j, s.pi2 j / s.pi1 j ∈
        Set.Icc (s.q1 * (s.lam2 - s.lam1) / s.lam2)
          (s.q1 * s.lam1 ^ 2 / (s.lam2 ^ 2 * s.q2 + s.lam1 * s.lam2 * (s.q1 - s.q2))) ∪
        Set.Icc 1 (s.q1 * s.lam1 ^ 2 / (s.lam2 * s.q2 ^ 2 * (s.lam2 - s.lam1)))) ∧
    (SustainableUC s ↔ ∀ j, s.pi2 j / s.pi1 j ∈
        Set.Icc 0 (s.q1 * s.lam1 / (s.lam2 - s.q2 * s.lam1)) ∪
        Set.Icc 1 (s.q1 * s.lam1 / (s.q2 * (s.lam2 - s.lam1)))) := by
  obtain ⟨hl1, hl12, hq1, hq1', hq2, hq2', hq, hp1, hp2, hs1, hs2⟩ := hs
  have hl2 : 0 < s.lam2 := by linarith
  have hfee : fee s = s.lam1 := by
    unfold fee
    rw [hs1, hs2]
    simp only [mul_one]
    exact min_eq_left hl12.le
  have hsolo : ∀ j, soloRevenue s j = max (min (s.lam1 * s.pi1 j) (s.lam2 * s.pi2 j))
      (max (s.q1 * (s.lam1 * s.pi1 j)) (s.q2 * (s.lam2 * s.pi2 j))) := fun j =>
    P4627.solo_eq s j hq1 hq1'.le hq2 hq2'.le (mul_nonneg hl1.le (hp1 j)) (mul_nonneg hl2.le (hp2 j))
  have hPR : ∀ β j, proRataPay s β j = β * (s.lam1 * (s.q1 * s.lam1 * s.pi1 j +
      s.q2 * s.lam2 * s.pi2 j) / (s.q1 * s.lam1 + s.q2 * s.lam2)) := by
    intro β j
    unfold proRataPay rev
    rw [hfee, hs1, hs2, hq]
    simp only [mul_one]
    ring
  have hUC : ∀ β j, userCentricPay s β j = β * (s.lam1 * (s.q1 * s.pi1 j + s.q2 * s.pi2 j)) := by
    intro β j
    unfold userCentricPay
    rw [hfee, ← Finset.mul_sum, ← Finset.mul_sum, hs1, hs2]
    simp only [mul_one]
    rw [mul_div_cancel_left₀ _ hl1.ne', mul_div_cancel_left₀ _ hl2.ne']
    ring
  have hPRnn : ∀ j, 0 ≤ s.lam1 * (s.q1 * s.lam1 * s.pi1 j + s.q2 * s.lam2 * s.pi2 j) /
      (s.q1 * s.lam1 + s.q2 * s.lam2) := by
    intro j
    have := hp1 j
    have := hp2 j
    positivity
  have hUCnn : ∀ j, 0 ≤ s.lam1 * (s.q1 * s.pi1 j + s.q2 * s.pi2 j) := by
    intro j
    have := hp1 j
    have := hp2 j
    positivity
  constructor
  · unfold SustainablePR
    constructor
    · rintro ⟨β, _, h1, h⟩ j
      rw [← P4627.key_pr s.lam1 s.lam2 s.q1 s.q2 (s.pi1 j) (s.pi2 j) hl1 hl12 hq1 hq2 hq (hpos j) (hp2 j),
        ← hsolo]
      exact (h j).trans (by rw [hPR]; exact mul_le_of_le_one_left (hPRnn j) h1)
    · intro h
      refine ⟨1, zero_le_one, le_rfl, fun j => ?_⟩
      rw [hPR, one_mul, hsolo]
      exact (P4627.key_pr s.lam1 s.lam2 s.q1 s.q2 (s.pi1 j) (s.pi2 j) hl1 hl12 hq1 hq2 hq (hpos j)
        (hp2 j)).2 (h j)
  · unfold SustainableUC
    constructor
    · rintro ⟨β, _, h1, h⟩ j
      rw [← P4627.key_uc s.lam1 s.lam2 s.q1 s.q2 (s.pi1 j) (s.pi2 j) hl1 hl12 hq1 hq2 hq (hpos j) (hp2 j),
        ← hsolo]
      exact (h j).trans (by rw [hUC]; exact mul_le_of_le_one_left (hUCnn j) h1)
    · intro h
      refine ⟨1, zero_le_one, le_rfl, fun j => ?_⟩
      rw [hUC, one_mul, hsolo]
      exact (P4627.key_uc s.lam1 s.lam2 s.q1 s.q2 (s.pi1 j) (s.pi2 j) hl1 hl12 hq1 hq2 hq (hpos j)
        (hp2 j)).2 (h j)
