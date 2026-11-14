-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.lemma_4_20_variational_limsup
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:00:39.347143+00:00
-- url     : https://prove2.me/submissions/66da8b8f-9f21-4045-a513-a59e38b148f0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20_log_first_moment
import Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20_first_limsup_from_log_bound
import Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_20_second_limsup
import Mathlib
open scoped Classical
open Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
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
              ∂(ν₀ : Measure (m.Spin → ℝ)) : ℝ) : EReal) := by
  intro s hs hs1
  obtain ⟨ν,hν,hmax,hupper⟩ := lemma_4_20_second_limsup m hm d hd t ht s hs hs1
  exact ⟨ν,hν,hmax,lemma_4_20_first_limsup_from_log_bound m hm d t s ht
    (lemma_4_20_log_first_moment m hm d hd t ht),hupper⟩
