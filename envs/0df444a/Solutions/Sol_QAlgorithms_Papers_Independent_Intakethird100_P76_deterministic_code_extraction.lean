-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P76.deterministic_code_extraction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:24:47.187298+00:00
-- url     : https://prove2.me/submissions/4f4af9d9-7719-4a5d-8a0e-937bf5cb82db

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P76

noncomputable section

open scoped BigOperators

open Filter Set

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

namespace Aux_P76_dce

theorem markov {C : Type*} [Fintype C] (p g : C → ℝ) (hp0 : ∀ c, 0 ≤ p c)
    (hg : ∀ c, 0 ≤ g c) :
    ∑ c ∈ Finset.univ.filter (fun c => 3 * (∑ d, p d * g d) < g c), p c ≤ 1 / 3 := by
  set m := ∑ d, p d * g d with hm
  set A := Finset.univ.filter (fun c => 3 * m < g c) with hA
  have hm0 : 0 ≤ m := Finset.sum_nonneg (fun d _ => mul_nonneg (hp0 d) (hg d))
  have h1 : ∑ c ∈ A, p c * (3 * m) ≤ ∑ c ∈ A, p c * g c := by
    apply Finset.sum_le_sum
    intro c hc
    have : 3 * m < g c := (Finset.mem_filter.1 hc).2
    exact mul_le_mul_of_nonneg_left this.le (hp0 c)
  have h2 : ∑ c ∈ A, p c * g c ≤ m := by
    rw [hm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun d _ _ => mul_nonneg (hp0 d) (hg d))
  rw [← Finset.sum_mul] at h1
  rcases hm0.lt_or_eq with hpos | hzero
  · nlinarith
  · have hz : ∀ c ∈ A, p c * g c = 0 := by
      have hsum : ∑ c ∈ A, p c * g c = 0 := by
        have h3 : 0 ≤ ∑ c ∈ A, p c * g c :=
          Finset.sum_nonneg (fun d _ => mul_nonneg (hp0 d) (hg d))
        linarith
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun d _ => mul_nonneg (hp0 d) (hg d))).1 hsum
    have hpz : ∀ c ∈ A, p c = 0 := by
      intro c hc
      have hgc : 0 < g c := by
        have : 3 * m < g c := (Finset.mem_filter.1 hc).2
        linarith
      have := hz c hc
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · linarith
    rw [Finset.sum_eq_zero hpz]
    norm_num

end Aux_P76_dce

open QAlgorithms.Papers.Independent.Intakethird100.P76 in
theorem solution {C : Type*} [Fintype C]
    (p e l : C → ℝ) (hp : IsLaw p) (he : ∀ c, 0 ≤ e c) (hl : ∀ c, 0 ≤ l c) :
    ∃ c, 0 < p c ∧ e c ≤ 3 * (∑ d, p d * e d) ∧
      l c ≤ 3 * (∑ d, p d * l d) := by
  obtain ⟨hp0, hp1⟩ := hp
  have hA := Aux_P76_dce.markov p e hp0 he
  have hB := Aux_P76_dce.markov p l hp0 hl
  by_contra hcon
  push_neg at hcon
  have hle : ∀ c, p c ≤
      (if 3 * (∑ d, p d * e d) < e c then p c else 0) +
        (if 3 * (∑ d, p d * l d) < l c then p c else 0) := by
    intro c
    rcases (hp0 c).lt_or_eq with hpos | hzero
    · by_cases hec : 3 * (∑ d, p d * e d) < e c
      · rw [if_pos hec]
        split_ifs <;> linarith [hp0 c]
      · have hlc : 3 * (∑ d, p d * l d) < l c := hcon c hpos (not_lt.1 hec)
        rw [if_neg hec, if_pos hlc]
        linarith
    · rw [← hzero]
      split_ifs <;> linarith
  have hsum : ∑ c, p c ≤
      ∑ c ∈ Finset.univ.filter (fun c => 3 * (∑ d, p d * e d) < e c), p c +
        ∑ c ∈ Finset.univ.filter (fun c => 3 * (∑ d, p d * l d) < l c), p c := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun c _ => hle c)
  linarith

end
