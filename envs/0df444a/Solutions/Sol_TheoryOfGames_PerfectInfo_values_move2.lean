-- Prove2me | solution 1 for TheoryOfGames.PerfectInfo.values_move2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T19:04:53.911543+00:00
-- url     : https://prove2.me/submissions/2a3ba3bd-86af-4871-ab4e-77ca43d83ccc

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values

open TheoryOfGames.PerfectInfo TheoryOfGames.PerfectInfo.GameTree in
theorem solution (α : ℕ) (hα : 0 < α) (next : Fin α → GameTree) :
    v1 (move2 α hα next) =
        Finset.univ.inf' ⟨⟨0, hα⟩, Finset.mem_univ _⟩ (fun σ : Fin α => v1 (next σ)) ∧
      v2 (move2 α hα next) =
        Finset.univ.inf' ⟨⟨0, hα⟩, Finset.mem_univ _⟩ (fun σ : Fin α => v2 (next σ)) := by
  classical
  let f0 : (σ : Fin α) → Strategy1 (next σ) := fun σ => Classical.arbitrary _
  let g0 : (σ : Fin α) → Strategy2 (next σ) := fun σ => Classical.arbitrary _
  constructor
  · apply le_antisymm
    · apply Finset.le_inf'
      intro σ _
      unfold v1
      apply Finset.sup'_le
      intro f _
      refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ
        ((f : (σ : Fin α) → Strategy1 (next σ)) σ)))
      apply Finset.le_inf'
      intro s₂ _
      refine le_trans (Finset.inf'_le _ (Finset.mem_univ
        (show Strategy2 (move2 α hα next) from (σ, Function.update g0 σ s₂)))) ?_
      show payoff (next σ) _ (Function.update g0 σ s₂ σ) ≤ _
      rw [Function.update_self]
    · have hmax : ∀ σ : Fin α, ∃ s₁ : Strategy1 (next σ),
          v1 (next σ) = Finset.univ.inf' Finset.univ_nonempty
            (fun s₂ : Strategy2 (next σ) => payoff (next σ) s₁ s₂) := by
        intro σ
        obtain ⟨s₁, _, h⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Strategy1 (next σ)))
          (fun s₁ : Strategy1 (next σ) => Finset.univ.inf' Finset.univ_nonempty
            (fun s₂ : Strategy2 (next σ) => payoff (next σ) s₁ s₂))
        exact ⟨s₁, h⟩
      choose f hf using hmax
      unfold v1
      refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ
        (show Strategy1 (move2 α hα next) from f)))
      apply Finset.le_inf'
      rintro ⟨σ₀, g⟩ _
      refine le_trans (Finset.inf'_le (fun σ : Fin α => v1 (next σ)) (Finset.mem_univ σ₀)) ?_
      show v1 (next σ₀) ≤ payoff (next σ₀) (f σ₀) (g σ₀)
      rw [hf σ₀]
      exact Finset.inf'_le (fun s₂ : Strategy2 (next σ₀) => payoff (next σ₀) (f σ₀) s₂)
        (Finset.mem_univ (g σ₀))
  · apply le_antisymm
    · apply Finset.le_inf'
      intro σ _
      unfold v2
      apply Finset.le_inf'
      intro s₂ _
      refine le_trans (Finset.inf'_le _ (Finset.mem_univ
        (show Strategy2 (move2 α hα next) from (σ, Function.update g0 σ s₂)))) ?_
      apply Finset.sup'_le
      intro τ₁ _
      refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ
        ((τ₁ : (σ : Fin α) → Strategy1 (next σ)) σ)))
      show payoff (next σ) _ (Function.update g0 σ s₂ σ) ≤ _
      rw [Function.update_self]
    · unfold v2
      apply Finset.le_inf'
      rintro ⟨σ₀, g⟩ _
      refine le_trans (Finset.inf'_le _ (Finset.mem_univ σ₀)) ?_
      refine le_trans (Finset.inf'_le _ (Finset.mem_univ (g σ₀))) ?_
      apply Finset.sup'_le
      intro s₁ _
      refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ
        (show Strategy1 (move2 α hα next) from Function.update f0 σ₀ s₁)))
      show _ ≤ payoff (next σ₀) (Function.update f0 σ₀ s₁ σ₀) (g σ₀)
      rw [Function.update_self]
