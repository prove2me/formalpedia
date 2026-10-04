-- Prove2me | solution 1 for TheoryOfGames.PerfectInfo.values_move1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T15:11:38.798209+00:00
-- url     : https://prove2.me/submissions/1084606c-e3fc-43c7-b8c7-5e9cb2415c3d

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values

open TheoryOfGames.PerfectInfo TheoryOfGames.PerfectInfo.GameTree in
theorem solution (α : ℕ) (hα : 0 < α) (next : Fin α → GameTree) :
    v1 (move1 α hα next) =
        Finset.univ.sup' ⟨⟨0, hα⟩, Finset.mem_univ _⟩ (fun σ : Fin α => v1 (next σ)) ∧
      v2 (move1 α hα next) =
        Finset.univ.sup' ⟨⟨0, hα⟩, Finset.mem_univ _⟩ (fun σ : Fin α => v2 (next σ)) := by
  classical
  let f0 : (σ : Fin α) → Strategy1 (next σ) := fun σ => Classical.arbitrary _
  let g0 : (σ : Fin α) → Strategy2 (next σ) := fun σ => Classical.arbitrary _
  constructor
  · apply le_antisymm
    · unfold v1
      apply Finset.sup'_le
      rintro ⟨σ₀, f⟩ _
      refine le_trans ?_ (Finset.le_sup' (fun σ : Fin α => v1 (next σ)) (Finset.mem_univ σ₀))
      unfold v1
      refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (f σ₀)))
      apply Finset.le_inf'
      intro s₂ _
      refine le_trans (Finset.inf'_le _ (Finset.mem_univ
        (show Strategy2 (move1 α hα next) from Function.update g0 σ₀ s₂))) ?_
      show payoff (next σ₀) (f σ₀) (Function.update g0 σ₀ s₂ σ₀) ≤ _
      rw [Function.update_self]
    · apply Finset.sup'_le
      intro σ _
      unfold v1
      apply Finset.sup'_le
      intro s₁ _
      refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ
        (show Strategy1 (move1 α hα next) from (σ, Function.update f0 σ s₁))))
      apply Finset.le_inf'
      intro τ₂ _
      refine le_trans (Finset.inf'_le _ (Finset.mem_univ
        ((τ₂ : (σ : Fin α) → Strategy2 (next σ)) σ))) ?_
      show _ ≤ payoff (next σ) (Function.update f0 σ s₁ σ) _
      rw [Function.update_self]
  · apply le_antisymm
    · have hmin : ∀ σ : Fin α, ∃ s₂ : Strategy2 (next σ),
          v2 (next σ) = Finset.univ.sup' Finset.univ_nonempty
            (fun s₁ : Strategy1 (next σ) => payoff (next σ) s₁ s₂) := by
        intro σ
        obtain ⟨s₂, _, h⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Strategy2 (next σ)))
          (fun s₂ : Strategy2 (next σ) => Finset.univ.sup' Finset.univ_nonempty
            (fun s₁ : Strategy1 (next σ) => payoff (next σ) s₁ s₂))
        exact ⟨s₂, h⟩
      choose g hg using hmin
      unfold v2
      refine le_trans (Finset.inf'_le _ (Finset.mem_univ
        (show Strategy2 (move1 α hα next) from g))) ?_
      apply Finset.sup'_le
      rintro ⟨σ₀, f⟩ _
      refine le_trans ?_ (Finset.le_sup' (fun σ : Fin α => v2 (next σ)) (Finset.mem_univ σ₀))
      show payoff (next σ₀) (f σ₀) (g σ₀) ≤ _
      rw [hg σ₀]
      exact Finset.le_sup' (fun s₁ : Strategy1 (next σ₀) => payoff (next σ₀) s₁ (g σ₀))
        (Finset.mem_univ (f σ₀))
    · apply Finset.sup'_le
      intro σ _
      unfold v2
      apply Finset.le_inf'
      intro τ₂ _
      refine le_trans (Finset.inf'_le _ (Finset.mem_univ
        ((τ₂ : (σ : Fin α) → Strategy2 (next σ)) σ))) ?_
      apply Finset.sup'_le
      intro s₁ _
      refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ
        (show Strategy1 (move1 α hα next) from (σ, Function.update f0 σ s₁))))
      show _ ≤ payoff (next σ) (Function.update f0 σ s₁ σ) _
      rw [Function.update_self]
