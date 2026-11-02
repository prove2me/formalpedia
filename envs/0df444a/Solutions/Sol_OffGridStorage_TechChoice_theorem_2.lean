-- Prove2me | solution 1 for OffGridStorage.TechChoice.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:10:01.093389+00:00
-- url     : https://prove2.me/submissions/94f3a4b6-fccf-44c2-861b-e9c5145c1871

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model
import Theorems.Thm_OffGridStorage_TechChoice_lemma_1_i
import Theorems.Thm_OffGridStorage_TechChoice_lemma_1_ii
import Theorems.Thm_OffGridStorage_TechChoice_eq_19_threshold_ratio

open OffGridStorage.TechChoice

theorem solution :
    (∀ T : ℕ, 1 ≤ T → ∀ A B : Tech, ValidTech A → ValidTech B →
      (Preferred T A B ↔ A.cK / A.e < B.cK / B.e)) ∧
    (∀ p : Params, Standing p →
      (OptimalStoragePos p ↔ p.cK / p.e < p.g - Real.sqrt (2 * p.cQ * p.g))) := by
  -- Γ^j described through the threshold g0 = g0ratio c_Q (c_K/e)
  have hGamma : ∀ T : ℕ, 1 ≤ T → ∀ j : Tech, ValidTech j → ∀ m : ℝ × ℝ × ℝ × ℝ,
      m ∈ Gamma T j ↔ MarketStanding m ∧ g0ratio m.1 (j.cK / j.e) < m.2.2.2 := by
    intro T hT j hj m
    constructor
    · rintro ⟨hm, hpos⟩
      have hst : Standing (withMarket T j m) := by
        obtain ⟨h1, h2, h3, h4⟩ := hm
        obtain ⟨j1, j2, j3⟩ := hj
        exact ⟨h2, h3, j1, j2, h1, j3, h4, hT⟩
      have := (lemma_1_i _ hst).1 hpos
      rw [lemma_1_ii.1] at this
      exact ⟨hm, this⟩
    · rintro ⟨hm, hlt⟩
      have hst : Standing (withMarket T j m) := by
        obtain ⟨h1, h2, h3, h4⟩ := hm
        obtain ⟨j1, j2, j3⟩ := hj
        exact ⟨h2, h3, j1, j2, h1, j3, h4, hT⟩
      refine ⟨hm, (lemma_1_i _ hst).2 ?_⟩
      rw [lemma_1_ii.1]
      exact hlt
  have hr : ∀ j : Tech, ValidTech j → 0 ≤ j.cK / j.e := fun j hj =>
    div_nonneg hj.2.2 hj.1.le
  refine ⟨?_, ?_⟩
  · intro T hT A B hA hB
    have hmono : ∀ cQ : ℝ, 0 < cQ → MonotoneOn (g0ratio cQ) (Set.Ici 0) :=
      fun cQ hcQ => (lemma_1_ii.2 cQ hcQ).monotoneOn
    constructor
    · intro hP
      by_contra hlt
      rw [not_lt] at hlt
      apply hP.2
      intro m hm
      rw [hGamma T hT A hA] at hm
      rw [hGamma T hT B hB]
      refine ⟨hm.1, lt_of_le_of_lt ?_ hm.2⟩
      exact hmono m.1 hm.1.1 (hr B hB) (hr A hA) hlt
    · intro hlt
      refine ⟨?_, ?_⟩
      · intro m hm
        rw [hGamma T hT B hB] at hm
        rw [hGamma T hT A hA]
        refine ⟨hm.1, lt_of_le_of_lt ?_ hm.2⟩
        exact hmono m.1 hm.1.1 (hr A hA) (hr B hB) hlt.le
      · intro hsub
        set rB := B.cK / B.e
        set rA := A.cK / A.e
        have hrA := hr A hA
        have hrBpos : 0 < rB := lt_of_le_of_lt hrA hlt
        let m : ℝ × ℝ × ℝ × ℝ := (1, 1, 1, g0ratio 1 rB)
        have hg : 2 * (1:ℝ) < g0ratio 1 rB := by
          unfold g0ratio
          have h1 : (1:ℝ) < Real.sqrt (1 ^ 2 + 2 * 1 * rB) := by
            rw [Real.lt_sqrt (by norm_num)]
            nlinarith
          linarith
        have hmA : m ∈ Gamma T A := by
          rw [hGamma T hT A hA]
          refine ⟨⟨by norm_num, by norm_num, by norm_num, hg⟩, ?_⟩
          exact lemma_1_ii.2 1 one_pos hrA hrBpos.le hlt
        have hmB := hsub hmA
        rw [hGamma T hT B hB] at hmB
        exact lt_irrefl _ hmB.2
  · intro p hp
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp
    rw [lemma_1_i p ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, lemma_1_ii.1]
    exact (eq_19_threshold_ratio p.cQ (p.cK / p.e) p.g h5 (div_nonneg h6 h3.le) h7).2
