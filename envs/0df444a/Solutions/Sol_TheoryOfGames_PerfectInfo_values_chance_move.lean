-- Prove2me | solution 1 for TheoryOfGames.PerfectInfo.values_chance_move
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T19:16:04.504978+00:00
-- url     : https://prove2.me/submissions/faa3ae5a-1426-4ac7-8d5c-86746d123a04

import Mathlib
import Definitions.Def_TheoryOfGames_PerfectInfo_Values

set_option autoImplicit false

namespace P2M5c768d32

lemma inf'_pi_sum {α : ℕ} {β : Fin α → Type} [∀ σ, Fintype (β σ)] [∀ σ, Nonempty (β σ)]
    [Fintype ((σ : Fin α) → β σ)] (hne : (Finset.univ : Finset ((σ : Fin α) → β σ)).Nonempty)
    (p : Fin α → ℝ) (hp : ∀ σ, 0 ≤ p σ) (f : ∀ σ, β σ → ℝ) :
    Finset.univ.inf' hne (fun x => ∑ σ, p σ * f σ (x σ)) =
      ∑ σ, p σ * Finset.univ.inf' Finset.univ_nonempty (f σ) := by
  apply le_antisymm
  · have hx : ∀ σ, ∃ y ∈ (Finset.univ : Finset (β σ)),
        Finset.univ.inf' Finset.univ_nonempty (f σ) = f σ y :=
      fun σ => Finset.exists_mem_eq_inf' Finset.univ_nonempty (f σ)
    choose y _ hy using hx
    calc Finset.univ.inf' hne (fun x => ∑ σ, p σ * f σ (x σ))
        ≤ ∑ σ, p σ * f σ (y σ) := Finset.inf'_le _ (Finset.mem_univ y)
      _ = _ := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [hy σ]
  · refine Finset.le_inf' _ _ fun x _ => ?_
    refine Finset.sum_le_sum fun σ _ => ?_
    exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ _)) (hp σ)

lemma sup'_pi_sum {α : ℕ} {β : Fin α → Type} [∀ σ, Fintype (β σ)] [∀ σ, Nonempty (β σ)]
    [Fintype ((σ : Fin α) → β σ)] (hne : (Finset.univ : Finset ((σ : Fin α) → β σ)).Nonempty)
    (p : Fin α → ℝ) (hp : ∀ σ, 0 ≤ p σ) (f : ∀ σ, β σ → ℝ) :
    Finset.univ.sup' hne (fun x => ∑ σ, p σ * f σ (x σ)) =
      ∑ σ, p σ * Finset.univ.sup' Finset.univ_nonempty (f σ) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun x _ => ?_
    refine Finset.sum_le_sum fun σ _ => ?_
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' _ (Finset.mem_univ _)) (hp σ)
  · have hx : ∀ σ, ∃ y ∈ (Finset.univ : Finset (β σ)),
        Finset.univ.sup' Finset.univ_nonempty (f σ) = f σ y :=
      fun σ => Finset.exists_mem_eq_sup' Finset.univ_nonempty (f σ)
    choose y _ hy using hx
    calc ∑ σ, p σ * Finset.univ.sup' Finset.univ_nonempty (f σ)
        = ∑ σ, p σ * f σ (y σ) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [hy σ]
      _ ≤ Finset.univ.sup' hne (fun x => ∑ σ, p σ * f σ (x σ)) :=
          Finset.le_sup' (fun x => ∑ σ, p σ * f σ (x σ)) (Finset.mem_univ y)

end P2M5c768d32

open TheoryOfGames.PerfectInfo TheoryOfGames.PerfectInfo.GameTree in
theorem solution (α : ℕ) (p : Fin α → ℝ) (next : Fin α → GameTree)
    (hp : ∀ σ, 0 ≤ p σ) (hsum : ∑ σ, p σ = 1) :
    v1 (chance α p next hp hsum) = ∑ σ, p σ * v1 (next σ) ∧
      v2 (chance α p next hp hsum) = ∑ σ, p σ * v2 (next σ) := by
  constructor
  · have e : v1 (chance α p next hp hsum) =
        Finset.univ.sup' Finset.univ_nonempty
          (fun τ₁ : (σ : Fin α) → Strategy1 (next σ) =>
            Finset.univ.inf' Finset.univ_nonempty
              (fun τ₂ : (σ : Fin α) → Strategy2 (next σ) =>
                ∑ σ, p σ * payoff (next σ) (τ₁ σ) (τ₂ σ))) := rfl
    rw [e]
    have h2 : ∀ τ₁ : (σ : Fin α) → Strategy1 (next σ),
        Finset.univ.inf' Finset.univ_nonempty
              (fun τ₂ : (σ : Fin α) → Strategy2 (next σ) =>
                ∑ σ, p σ * payoff (next σ) (τ₁ σ) (τ₂ σ)) =
          ∑ σ, p σ * Finset.univ.inf' Finset.univ_nonempty (fun y => payoff (next σ) (τ₁ σ) y) :=
      fun τ₁ => P2M5c768d32.inf'_pi_sum _ p hp (fun σ y => payoff (next σ) (τ₁ σ) y)
    simp_rw [h2]
    exact P2M5c768d32.sup'_pi_sum _ p hp
      (fun σ x => Finset.univ.inf' Finset.univ_nonempty (fun y => payoff (next σ) x y))
  · have e : v2 (chance α p next hp hsum) =
        Finset.univ.inf' Finset.univ_nonempty
          (fun τ₂ : (σ : Fin α) → Strategy2 (next σ) =>
            Finset.univ.sup' Finset.univ_nonempty
              (fun τ₁ : (σ : Fin α) → Strategy1 (next σ) =>
                ∑ σ, p σ * payoff (next σ) (τ₁ σ) (τ₂ σ))) := rfl
    rw [e]
    have h2 : ∀ τ₂ : (σ : Fin α) → Strategy2 (next σ),
        Finset.univ.sup' Finset.univ_nonempty
              (fun τ₁ : (σ : Fin α) → Strategy1 (next σ) =>
                ∑ σ, p σ * payoff (next σ) (τ₁ σ) (τ₂ σ)) =
          ∑ σ, p σ * Finset.univ.sup' Finset.univ_nonempty (fun x => payoff (next σ) x (τ₂ σ)) :=
      fun τ₂ => P2M5c768d32.sup'_pi_sum _ p hp (fun σ x => payoff (next σ) x (τ₂ σ))
    simp_rw [h2]
    exact P2M5c768d32.inf'_pi_sum _ p hp
      (fun σ y => Finset.univ.sup' Finset.univ_nonempty (fun x => payoff (next σ) x y))
