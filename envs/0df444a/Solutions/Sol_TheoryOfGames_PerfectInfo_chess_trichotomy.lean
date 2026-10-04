-- Prove2me | solution 1 for TheoryOfGames.PerfectInfo.chess_trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:45:53.199838+00:00
-- url     : https://prove2.me/submissions/07d63b72-5af7-479b-aa43-735b10e1a7ea

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values
import Definitions.Def_TheoryOfGames_PerfectInfo_ChessLike

set_option autoImplicit false

namespace P2M158f1ba6

open TheoryOfGames.PerfectInfo TheoryOfGames.PerfectInfo.GameTree

theorem payoff_bounds (t : GameTree) (hnc : NoChanceMoves t) (hout : OutcomesWinTieLoss t) :
    ∀ (τ₁ : Strategy1 t) (τ₂ : Strategy2 t), -1 ≤ payoff t τ₁ τ₂ ∧ payoff t τ₁ τ₂ ≤ 1 := by
  induction t with
  | leaf w =>
    intro τ₁ τ₂
    simp only [OutcomesWinTieLoss] at hout
    simp only [payoff]
    rcases hout with h | h | h <;> subst h <;> norm_num
  | chance α p next hp hsum ih =>
    simp only [NoChanceMoves] at hnc
  | move1 α hα next ih =>
    simp only [NoChanceMoves] at hnc
    simp only [OutcomesWinTieLoss] at hout
    intro τ₁ τ₂
    simp only [payoff]
    exact ih _ (hnc _) (hout _) _ _
  | move2 α hα next ih =>
    simp only [NoChanceMoves] at hnc
    simp only [OutcomesWinTieLoss] at hout
    intro τ₁ τ₂
    simp only [payoff]
    exact ih _ (hnc _) (hout _) _ _

theorem determined (t : GameTree) (hnc : NoChanceMoves t) (hout : OutcomesWinTieLoss t) :
    ∃ c : ℝ, (c = 1 ∨ c = 0 ∨ c = -1) ∧
      (∃ τ₁ : Strategy1 t, ∀ τ₂ : Strategy2 t, c ≤ payoff t τ₁ τ₂) ∧
      (∃ τ₂ : Strategy2 t, ∀ τ₁ : Strategy1 t, payoff t τ₁ τ₂ ≤ c) := by
  induction t with
  | leaf w =>
    simp only [OutcomesWinTieLoss] at hout
    exact ⟨w, hout, ⟨(), fun _ => le_refl _⟩, ⟨(), fun _ => le_refl _⟩⟩
  | chance α p next hp hsum ih =>
    simp only [NoChanceMoves] at hnc
  | move1 α hα next ih =>
    simp only [NoChanceMoves] at hnc
    simp only [OutcomesWinTieLoss] at hout
    have H : ∀ σ, ∃ c : ℝ, (c = 1 ∨ c = 0 ∨ c = -1) ∧
        (∃ τ₁ : Strategy1 (next σ), ∀ τ₂ : Strategy2 (next σ), c ≤ payoff (next σ) τ₁ τ₂) ∧
        (∃ τ₂ : Strategy2 (next σ), ∀ τ₁ : Strategy1 (next σ), payoff (next σ) τ₁ τ₂ ≤ c) :=
      fun σ => ih σ (hnc σ) (hout σ)
    choose c hc0 using H
    have hc : ∀ σ, c σ = 1 ∨ c σ = 0 ∨ c σ = -1 := fun σ => (hc0 σ).1
    choose f₁ hf₁ using fun σ => (hc0 σ).2.1
    choose f₂ hf₂ using fun σ => (hc0 σ).2.2
    obtain ⟨s, -, hs⟩ := Finset.exists_max_image Finset.univ c ⟨⟨0, hα⟩, Finset.mem_univ _⟩
    refine ⟨c s, hc s, ⟨(⟨s, f₁⟩ : Fin α × ((σ : Fin α) → Strategy1 (next σ))), ?_⟩,
      ⟨(f₂ : (σ : Fin α) → Strategy2 (next σ)), ?_⟩⟩
    · intro τ₂
      simp only [payoff]
      exact hf₁ s _
    · intro τ₁
      obtain ⟨u, g⟩ := (τ₁ : Fin α × ((σ : Fin α) → Strategy1 (next σ)))
      simp only [payoff]
      exact (hf₂ u _).trans (hs u (Finset.mem_univ _))
  | move2 α hα next ih =>
    simp only [NoChanceMoves] at hnc
    simp only [OutcomesWinTieLoss] at hout
    have H : ∀ σ, ∃ c : ℝ, (c = 1 ∨ c = 0 ∨ c = -1) ∧
        (∃ τ₁ : Strategy1 (next σ), ∀ τ₂ : Strategy2 (next σ), c ≤ payoff (next σ) τ₁ τ₂) ∧
        (∃ τ₂ : Strategy2 (next σ), ∀ τ₁ : Strategy1 (next σ), payoff (next σ) τ₁ τ₂ ≤ c) :=
      fun σ => ih σ (hnc σ) (hout σ)
    choose c hc0 using H
    have hc : ∀ σ, c σ = 1 ∨ c σ = 0 ∨ c σ = -1 := fun σ => (hc0 σ).1
    choose f₁ hf₁ using fun σ => (hc0 σ).2.1
    choose f₂ hf₂ using fun σ => (hc0 σ).2.2
    obtain ⟨s, -, hs⟩ := Finset.exists_min_image Finset.univ c ⟨⟨0, hα⟩, Finset.mem_univ _⟩
    refine ⟨c s, hc s, ⟨(f₁ : (σ : Fin α) → Strategy1 (next σ)), ?_⟩,
      ⟨(⟨s, f₂⟩ : Fin α × ((σ : Fin α) → Strategy2 (next σ))), ?_⟩⟩
    · intro τ₂
      obtain ⟨u, g⟩ := (τ₂ : Fin α × ((σ : Fin α) → Strategy2 (next σ)))
      simp only [payoff]
      exact (hs u (Finset.mem_univ _)).trans (hf₁ u _)
    · intro τ₁
      simp only [payoff]
      exact hf₂ s _

theorem v1_eq (t : GameTree) (c : ℝ) (τ₁ : Strategy1 t) (h₁ : ∀ τ₂ : Strategy2 t, c ≤ payoff t τ₁ τ₂)
    (τ₂ : Strategy2 t) (h₂ : ∀ τ₁ : Strategy1 t, payoff t τ₁ τ₂ ≤ c) : v1 t = c := by
  unfold v1
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    exact Finset.inf'_le_of_le _ (Finset.mem_univ τ₂) (h₂ a)
  · apply Finset.le_sup'_of_le _ (Finset.mem_univ τ₁)
    apply Finset.le_inf'
    intro b _
    exact h₁ b

end P2M158f1ba6

open TheoryOfGames.PerfectInfo GameTree in
theorem solution (t : GameTree) (hnc : NoChanceMoves t)
    (hout : OutcomesWinTieLoss t) :
    (v1 t = 1 ∨ v1 t = 0 ∨ v1 t = -1) ∧
      (v1 t = 1 → ∃ τ₁ : Strategy1 t, ∀ τ₂ : Strategy2 t, payoff t τ₁ τ₂ = 1) ∧
      (v1 t = 0 → (∃ τ₁ : Strategy1 t, ∀ τ₂ : Strategy2 t, 0 ≤ payoff t τ₁ τ₂) ∧
        (∃ τ₂ : Strategy2 t, ∀ τ₁ : Strategy1 t, payoff t τ₁ τ₂ ≤ 0)) ∧
      (v1 t = -1 → ∃ τ₂ : Strategy2 t, ∀ τ₁ : Strategy1 t, payoff t τ₁ τ₂ = -1) := by
  obtain ⟨c, hc, ⟨τ₁, h₁⟩, ⟨τ₂, h₂⟩⟩ := P2M158f1ba6.determined t hnc hout
  have hv : v1 t = c := P2M158f1ba6.v1_eq t c τ₁ h₁ τ₂ h₂
  have hb := P2M158f1ba6.payoff_bounds t hnc hout
  rw [hv]
  refine ⟨hc, ?_, ?_, ?_⟩
  · intro h1
    subst h1
    exact ⟨τ₁, fun b => le_antisymm (hb τ₁ b).2 (h₁ b)⟩
  · intro h0
    subst h0
    exact ⟨⟨τ₁, h₁⟩, ⟨τ₂, h₂⟩⟩
  · intro hm
    subst hm
    exact ⟨τ₂, fun a => le_antisymm (h₂ a) (hb a τ₂).1⟩
