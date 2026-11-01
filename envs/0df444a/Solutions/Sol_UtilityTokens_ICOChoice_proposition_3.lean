-- Prove2me | solution 1 for UtilityTokens.ICOChoice.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:48:53.943139+00:00
-- url     : https://prove2.me/submissions/a88fed38-cf11-46f9-ae96-e52b1cf3aa76

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting
import Theorems.Thm_UtilityTokens_ICOChoice_proposition_1
import Theorems.Thm_UtilityTokens_ICOChoice_proposition_2
import Theorems.Thm_UtilityTokens_ICOChoice_lemma_1

open UtilityTokens.ICOChoice

theorem solution (Θ x f : ℝ) (hΘ : UtilityTokens.ICOChoice.thetaTilde < Θ) (hΘ3 : Θ ≤ 3)
    (hx : 0 < x) :
    (∃ c ∈ UtilityTokens.ICOChoice.ICOChoices Θ x, ∀ c' ∈ UtilityTokens.ICOChoice.ICOChoices Θ x,
        UtilityTokens.ICOChoice.profitI Θ x f c'.1 c'.2 ≤
          UtilityTokens.ICOChoice.profitI Θ x f c.1 c.2) ∧
    (∀ c ∈ UtilityTokens.ICOChoice.ICOChoices Θ x,
        (∀ c' ∈ UtilityTokens.ICOChoice.ICOChoices Θ x,
          UtilityTokens.ICOChoice.profitI Θ x f c'.1 c'.2 ≤
            UtilityTokens.ICOChoice.profitI Θ x f c.1 c.2) → 1 < c.1) ∧
    (∀ θbar ∈ Set.Icc 1 Θ,
        (∀ θ' ∈ Set.Icc 1 Θ, UtilityTokens.ICOChoice.profitT Θ x θ' ≤
          UtilityTokens.ICOChoice.profitT Θ x θbar) → θbar = 1) := by
  obtain ⟨_, ⟨h1T, _⟩, _, hgt, _⟩ := lemma_1
  have hT1 : 1 < Θ := lt_trans h1T hΘ
  obtain ⟨_, ⟨⟨c0, hc0, hc0v⟩, hub⟩, _, huniq, _, _⟩ := proposition_2 Θ x f hT1 hx
  obtain ⟨⟨⟨t0, ht0, ht0v⟩, hubT⟩, huniqT, _, _⟩ := proposition_1 Θ x hT1 hΘ3 hx
  refine ⟨⟨c0, hc0, fun c' hc' => ?_⟩, fun c hc hmax => ?_, fun θbar hθ hmax => ?_⟩
  · simp only at hc0v
    rw [hc0v]
    exact hub ⟨c', hc', rfl⟩
  · have h1 := hmax c0 hc0
    have h2 := hub ⟨c, hc, rfl⟩
    simp only at hc0v h1 h2
    have := huniq c hc (le_antisymm h2 (hc0v ▸ h1))
    rw [this]; exact hgt Θ hΘ
  · have h1 := hmax t0 ht0
    have h2 := hubT ⟨θbar, hθ, rfl⟩
    rw [ht0v] at h1
    exact huniqT θbar hθ (le_antisymm h2 h1)
