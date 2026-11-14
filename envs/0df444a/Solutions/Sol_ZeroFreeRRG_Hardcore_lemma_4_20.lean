-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.lemma_4_20
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:47:39.719141+00:00
-- url     : https://prove2.me/submissions/92e86b8d-33e0-4f1b-9625-8b9866cc70d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20_log_first_moment
import Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20_pinned_concentration
import Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20_variational_limsup
import Mathlib
open scoped Classical
open Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t) :
    (∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
        |Real.log (an m d n t)| ≤ C * Real.log (n + 1)) ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ b : ℝ, 0 < b → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, Even (n * d) →
        plantedPinnedE m t s d n (fun M σ U =>
            if pinnedLL m t M σ U - plantedPinnedE m t s d n (fun M' σ' U' => pinnedLL m t M' σ' U')
                > b * n then 1 else 0) ≤ Real.exp (-c * n)) ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∃ ν₀ ∈ cavityLaws m t,
        (∀ ν ∈ cavityLaws m t,
          betheK m t d ν + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
              ∂(ν : Measure (m.Spin → ℝ)) ≤
          betheK m t d ν₀ + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
              ∂(ν₀ : Measure (m.Spin → ℝ))) ∧
        limsup (fun n : ℕ => (((1 : ℝ) / n *
            plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) : ℝ) : EReal))
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) ≤
          limsup (fun n : ℕ => (((1 : ℝ) / n *
            plantedPinnedE m t s d n (fun M σ U => Real.log (normZ m t M) + pinnedLL m t M σ U)
              : ℝ) : EReal))
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) ∧
        limsup (fun n : ℕ => (((1 : ℝ) / n *
            plantedPinnedE m t s d n (fun M σ U => Real.log (normZ m t M) + pinnedLL m t M σ U)
              : ℝ) : EReal))
            (atTop ⊓ 𝓟 {n : ℕ | Even (n * d)}) ≤
          ((betheK m t d ν₀ + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
              ∂(ν₀ : Measure (m.Spin → ℝ)) : ℝ) : EReal)) := by
  exact ⟨lemma_4_20_log_first_moment m hm d hd t ht, lemma_4_20_pinned_concentration m hm d hd t ht,
    lemma_4_20_variational_limsup m hm d hd t ht⟩
