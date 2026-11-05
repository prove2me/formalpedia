-- Prove2me | solution 1 for QualityEncroach.Differ.proposition_1_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:39:58.522353+00:00
-- url     : https://prove2.me/submissions/557e4804-e236-4fa7-9ae8-6664a49c75f4

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game
import Theorems.Thm_QualityEncroach_Uniform_proposition_1_iii

open QualityEncroach.Differ

theorem solution (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (σ : Profile)
    (hσ : IsSPE k c {1} σ) (henc : 0 < σ.path.qM) :
    1 / (54 * k) < mfrPayoff k c σ.path ∧ retailerPayoff σ.path < 1 / (108 * k) := by
  obtain ⟨h3, h2, hu, ht, h1⟩ := hσ
  have ht1 : σ.t = 1 := Set.mem_singleton_iff.mp ht
  have h1' : (1 : ℝ) ∈ ({1} : Set ℝ) := Set.mem_singleton 1
  -- the corresponding profile of the uniform-quality game
  let τ : QualityEncroach.Uniform.Profile :=
    ⟨σ.w, σ.u, fun w u => σ.order w u 1, fun w u qR => σ.direct w u 1 qR⟩
  have hM : ∀ w u qR qM : ℝ,
      mfrPayoff k c ⟨w, u, 1, qR, qM⟩ = QualityEncroach.Uniform.mfrPayoff k c ⟨w, u, qR, qM⟩ := by
    intro w u qR qM
    simp only [mfrPayoff, QualityEncroach.Uniform.mfrPayoff, priceM, le_refl, if_true]
    ring
  have hR : ∀ w u qR qM : ℝ,
      retailerPayoff ⟨w, u, 1, qR, qM⟩ = QualityEncroach.Uniform.retailerPayoff ⟨w, u, qR, qM⟩ := by
    intro w u qR qM
    simp only [retailerPayoff, QualityEncroach.Uniform.retailerPayoff, priceR, le_refl, if_true]
    ring
  have hpath : σ.path = ⟨σ.w, σ.u, 1, τ.path.qR, τ.path.qM⟩ := by
    simp only [Profile.path, Profile.outcomeAtOrder, Profile.outcomeAtDirect, τ,
      QualityEncroach.Uniform.Profile.path, QualityEncroach.Uniform.Profile.outcomeAtOrder,
      QualityEncroach.Uniform.Profile.outcomeAtDirect, ht1]
  have hτpath : τ.path = ⟨σ.w, σ.u, τ.path.qR, τ.path.qM⟩ := rfl
  have hτ : QualityEncroach.Uniform.IsSPE k c τ := by
    refine ⟨?_, ?_, hu, ?_⟩
    · intro w u qR hu' hqR
      obtain ⟨a, b⟩ := h3 w u 1 qR hu' h1' hqR
      refine ⟨a, fun qM hqM => ?_⟩
      have := b qM hqM
      rw [hM] at this
      simpa [Profile.outcomeAtDirect, hM, τ, QualityEncroach.Uniform.Profile.outcomeAtDirect]
        using this
    · intro w u hu'
      obtain ⟨a, b⟩ := h2 w u 1 hu' h1'
      refine ⟨a, fun qR hqR => ?_⟩
      have := b qR hqR
      simpa [Profile.outcomeAtDirect, Profile.outcomeAtOrder, hR, τ,
        QualityEncroach.Uniform.Profile.outcomeAtDirect,
        QualityEncroach.Uniform.Profile.outcomeAtOrder] using this
    · intro w u hu'
      have := h1 w u 1 hu' h1'
      rw [hpath] at this
      simpa [Profile.outcomeAtDirect, Profile.outcomeAtOrder, hM, τ,
        QualityEncroach.Uniform.Profile.outcomeAtDirect,
        QualityEncroach.Uniform.Profile.outcomeAtOrder,
        QualityEncroach.Uniform.Profile.path] using this
  have henc' : 0 < τ.path.qM := by
    rw [hpath] at henc; exact henc
  have key := QualityEncroach.Uniform.proposition_1_iii k c hk hc τ hτ henc'
  rw [hpath, hM, hR]
  exact key
