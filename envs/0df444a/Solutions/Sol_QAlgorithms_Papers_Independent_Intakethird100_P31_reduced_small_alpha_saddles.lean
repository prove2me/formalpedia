-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P31.reduced_small_alpha_saddles
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:32:00.774204+00:00
-- url     : https://prove2.me/submissions/df457b21-2232-478e-8e5f-1979a3fa5b00

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P31

noncomputable section

open Filter Set MeasureTheory

open scoped Topology BigOperators

open QAlgorithms.Papers.Independent.Intakethird100.P31 in
theorem solution (N : ℕ) (hN : 0 < N)
    (eps n : ℝ) (heps : 0 < eps) (hD : eps < 2) (hn : 0 < n) :
    (∀ alpha : ℝ, reducedGap eps n alpha = 0 ↔
      0 ≤ reducedDiscriminant eps n ∧
        (alpha = reducedRoot eps n true ∨ alpha = reducedRoot eps n false)) ∧
    (0 ≤ reducedDiscriminant eps n ↔ n ≤ Real.sqrt (1 + 3 * eps / 2)) ∧
    (0 ≤ reducedDiscriminant eps n →
      ((reducedRoot eps n true = reducedRoot eps n false ↔
          reducedDiscriminant eps n = 0) ∧
       (∀ plus : Bool,
         reducedAmplitude N eps (reducedRoot eps n plus) =
           (N : ℝ) / (8 * Real.pi ^ 2) *
             ((1 / n ^ 2 - 1) / 6 +
               (eps - (if plus then 1 else -1) *
                 Real.sqrt (reducedDiscriminant eps n)) / (2 * n ^ 2))))) ∧
    Tendsto (fun e : ℝ => (Real.sqrt (1 + 3 * e / 2) - 1) / e)
      (𝓝[>] (0 : ℝ)) (𝓝 (3 / 4 : ℝ)) := by
  have hn0 : n ≠ 0 := hn.ne'
  have heps0 : eps ≠ 0 := heps.ne'
  have h2n : 2 * n ≠ 0 := mul_ne_zero two_ne_zero hn0
  have h4 : 4 * n ^ 2 * eps ≠ 0 := mul_ne_zero (mul_ne_zero four_ne_zero (pow_ne_zero 2 hn0)) heps0
  have key : ∀ α : ℝ, reducedGap eps n α * (4 * n ^ 2 * eps) =
      (2 * n * α + eps) ^ 2 - reducedDiscriminant eps n := by
    intro α
    unfold reducedGap reducedDiscriminant
    field_simp <;> ring
  have hr : ∀ plus : Bool, 2 * n * reducedRoot eps n plus + eps =
      (if plus then 1 else -1) * Real.sqrt (reducedDiscriminant eps n) := by
    intro plus
    unfold reducedRoot
    rw [← add_div, mul_div_cancel₀ _ h2n]
    ring
  have hT : 2 * n * reducedRoot eps n true + eps = Real.sqrt (reducedDiscriminant eps n) := by
    have := hr true
    rwa [if_pos rfl, one_mul] at this
  have hF : 2 * n * reducedRoot eps n false + eps = -Real.sqrt (reducedDiscriminant eps n) := by
    have := hr false
    rwa [if_neg Bool.false_ne_true, neg_one_mul] at this
  have hiffT : ∀ α : ℝ, α = reducedRoot eps n true ↔
      2 * n * α + eps = Real.sqrt (reducedDiscriminant eps n) := by
    intro α
    constructor
    · intro h; rw [h, hT]
    · intro h
      apply mul_left_cancel₀ h2n
      linarith
  have hiffF : ∀ α : ℝ, α = reducedRoot eps n false ↔
      2 * n * α + eps = -Real.sqrt (reducedDiscriminant eps n) := by
    intro α
    constructor
    · intro h; rw [h, hF]
    · intro h
      apply mul_left_cancel₀ h2n
      linarith
  have part1 : ∀ alpha : ℝ, reducedGap eps n alpha = 0 ↔
      0 ≤ reducedDiscriminant eps n ∧
        (alpha = reducedRoot eps n true ∨ alpha = reducedRoot eps n false) := by
    intro α
    rw [hiffT α, hiffF α]
    constructor
    · intro h0
      have hsq : (2 * n * α + eps) ^ 2 = reducedDiscriminant eps n := by
        have hk := key α
        rw [h0, zero_mul] at hk
        linarith
      have hD0 : 0 ≤ reducedDiscriminant eps n := by
        rw [← hsq]; exact sq_nonneg _
      refine ⟨hD0, ?_⟩
      have habs : Real.sqrt (reducedDiscriminant eps n) = |2 * n * α + eps| := by
        rw [← hsq, Real.sqrt_sq_eq_abs]
      rcases abs_cases (2 * n * α + eps) with ⟨h1, _⟩ | ⟨h1, _⟩
      · left; rw [habs, h1]
      · right; rw [habs, h1]; ring
    · rintro ⟨hD0, h | h⟩
      · have hsq : (2 * n * α + eps) ^ 2 = reducedDiscriminant eps n := by
          rw [h, Real.sq_sqrt hD0]
        have hk := key α
        rw [hsq, sub_self] at hk
        exact (mul_eq_zero.mp hk).resolve_right h4
      · have hsq : (2 * n * α + eps) ^ 2 = reducedDiscriminant eps n := by
          rw [h, neg_sq, Real.sq_sqrt hD0]
        have hk := key α
        rw [hsq, sub_self] at hk
        exact (mul_eq_zero.mp hk).resolve_right h4
  have part2 : 0 ≤ reducedDiscriminant eps n ↔ n ≤ Real.sqrt (1 + 3 * eps / 2) := by
    rw [Real.le_sqrt hn.le (by linarith)]
    unfold reducedDiscriminant
    constructor
    · intro h
      by_contra hc
      push_neg at hc
      nlinarith
    · intro h
      nlinarith
  have part4 : Tendsto (fun e : ℝ => (Real.sqrt (1 + 3 * e / 2) - 1) / e)
      (𝓝[>] (0 : ℝ)) (𝓝 (3 / 4 : ℝ)) := by
    have hc : Continuous (fun e : ℝ => Real.sqrt (1 + 3 * e / 2) + 1) := by
      fun_prop
    have hcont : ContinuousAt (fun e : ℝ => (3 / 2 : ℝ) / (Real.sqrt (1 + 3 * e / 2) + 1)) 0 := by
      apply ContinuousAt.div continuousAt_const hc.continuousAt
      positivity
    have hlim : Tendsto (fun e : ℝ => (3 / 2 : ℝ) / (Real.sqrt (1 + 3 * e / 2) + 1))
        (𝓝[>] (0 : ℝ)) (𝓝 (3 / 4 : ℝ)) := by
      have h0 : (3 / 2 : ℝ) / (Real.sqrt (1 + 3 * 0 / 2) + 1) = 3 / 4 := by
        norm_num
      rw [← h0]
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    have he' : 0 < e := he
    have hs : Real.sqrt (1 + 3 * e / 2) ^ 2 = 1 + 3 * e / 2 := Real.sq_sqrt (by linarith)
    have hs0 : 0 ≤ Real.sqrt (1 + 3 * e / 2) := Real.sqrt_nonneg _
    rw [div_eq_div_iff (by positivity) he'.ne']
    nlinarith
  refine ⟨part1, part2, ?_, part4⟩
  intro hD0
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      have h1 := hT
      rw [h, hF] at h1
      have h2 : Real.sqrt (reducedDiscriminant eps n) = 0 := by linarith
      exact (Real.sqrt_eq_zero hD0).mp h2
    · intro h
      have h1 := hT
      have h2 := hF
      rw [h, Real.sqrt_zero] at h1 h2
      apply mul_left_cancel₀ h2n
      linarith
  · intro plus
    have hg : reducedGap eps n (reducedRoot eps n plus) = 0 :=
      (part1 _).mpr ⟨hD0, by cases plus <;> simp⟩
    have hrp := hr plus
    obtain ⟨r, hrdef⟩ : ∃ r, r = reducedRoot eps n plus := ⟨_, rfl⟩
    obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (if plus then 1 else -1) := ⟨_, rfl⟩
    obtain ⟨sD, hsD⟩ : ∃ sD, sD = Real.sqrt (reducedDiscriminant eps n) := ⟨_, rfl⟩
    rw [← hrdef] at hg hrp ⊢
    rw [← hcdef, ← hsD] at hrp
    rw [← hcdef, ← hsD]
    unfold reducedGap at hg
    unfold reducedAmplitude
    have e1 : r ^ 2 / eps = (1 / n ^ 2 - 1) / 6 - r / n := by linarith
    have e2 : r ^ 2 = eps * ((1 / n ^ 2 - 1) / 6 - r / n) := by
      rw [← e1]; field_simp
    have hrv : r = (c * sD - eps) / (2 * n) := by
      rw [eq_div_iff h2n]; linarith
    rw [e2, hrv]
    field_simp <;> ring

end
