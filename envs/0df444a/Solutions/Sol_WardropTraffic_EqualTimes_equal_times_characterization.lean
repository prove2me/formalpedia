-- Prove2me | solution 1 for WardropTraffic.EqualTimes.equal_times_characterization
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:23:27.417993+00:00
-- url     : https://prove2.me/submissions/75adb5f6-9e0a-425f-a844-3d3d999af79f

import Mathlib
import Definitions.Def_WardropTraffic_EqualTimes_Setting

open WardropTraffic.EqualTimes

private lemma used_flow {D : ℕ} (b p : Fin D → ℝ) (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i)
    (Q t : ℝ) (q : Fin D → ℝ) (h : IsEqualTimes b p Q q t) (i : Fin D) (hi : 0 < q i) :
    b i < t ∧ q i = p i * (1 - b i / t) := by
  have hd : 0 < 1 - q i / p i := by
    have := (div_lt_one (hp i)).mpr (h.1.1 i).2
    linarith
  have ht := h.2.1 i hi
  unfold routeTime at ht
  have htp : 0 < t := ht ▸ div_pos (hb i) hd
  have he := (div_eq_iff (ne_of_gt hd)).mp ht
  have hbt : b i < t := by
    rw [← ht]
    apply (lt_div_iff₀ hd).mpr
    have := mul_pos (hb i) (div_pos hi (hp i))
    nlinarith
  refine ⟨hbt, ?_⟩
  have hp0 := ne_of_gt (hp i)
  have ht0 := ne_of_gt htp
  field_simp at he ⊢
  nlinarith [he]

theorem solution {D : ℕ} (b p : Fin D → ℝ) (hb : ∀ i, 0 < b i)
    (hp : ∀ i, 0 < p i) (Q t : ℝ) (q : Fin D → ℝ) :
    IsEqualTimes b p Q q t ↔
      ((∀ i, q i = if b i < t then p i * (1 - b i / t) else 0) ∧
        Q = ∑ i ∈ usedSet b t, p i - (1 / t) * ∑ i ∈ usedSet b t, p i * b i) := by
  classical
  have hs : (∑ i, if b i < t then p i * (1 - b i / t) else 0) =
      ∑ i ∈ usedSet b t, p i - (1 / t) * ∑ i ∈ usedSet b t, p i * b i := by
    rw [← Finset.sum_filter]
    unfold usedSet
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  constructor
  · intro h
    have hq : ∀ i, q i = if b i < t then p i * (1 - b i / t) else 0 := by
      intro i
      by_cases hi : 0 < q i
      · have hh := used_flow b p hb hp Q t q h i hi
        simp [hh.1, hh.2]
      · have hz : q i = 0 := by linarith [(h.1.1 i).1]
        have hbt := h.2.2 i hz
        simp [hz, not_lt.mpr hbt]
    refine ⟨hq, ?_⟩
    rw [← h.1.2]
    simpa only [hq] using hs
  · rintro ⟨hq, hQ⟩
    have hfeas : ∀ i, 0 ≤ q i ∧ q i < p i := by
      intro i
      rw [hq i]
      split_ifs with hi
      · have ht : 0 < t := lt_trans (hb i) hi
        have hdiv : b i / t < 1 := (div_lt_one ht).mpr hi
        have hdiv0 : 0 < b i / t := div_pos (hb i) ht
        constructor
        · exact (mul_pos (hp i) (sub_pos.mpr hdiv)).le
        · nlinarith [mul_pos (hp i) hdiv0]
      · exact ⟨le_rfl, hp i⟩
    refine ⟨⟨hfeas, ?_⟩, ?_, ?_⟩
    · rw [hQ]
      simpa only [hq] using hs
    · intro i hi
      have hbt : b i < t := by
        by_contra hh
        have hz : q i = 0 := by simp [hq i, hh]
        linarith
      have ht : 0 < t := lt_trans (hb i) hbt
      unfold routeTime
      rw [hq i, if_pos hbt]
      have hp0 := ne_of_gt (hp i)
      have ht0 := ne_of_gt ht
      field_simp [hp0, ht0, ne_of_gt (hb i)]
      ring
    · intro i hz
      by_contra hh
      have hbt : b i < t := lt_of_not_ge hh
      have ht : 0 < t := lt_trans (hb i) hbt
      have hd : 0 < 1 - b i / t := sub_pos.mpr ((div_lt_one ht).mpr hbt)
      have hpos : 0 < q i := by rw [hq i, if_pos hbt]; exact mul_pos (hp i) hd
      linarith

#print axioms solution
