-- Prove2me | solution 1 for OnlineRandomization.Simulation.one_step_winning
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:57:44.476894+00:00
-- url     : https://prove2.me/submissions/a7ae48c7-4ecc-4974-a612-b78b99d192af

import Mathlib
import Definitions.Def_OnlineRandomization_Simulation_Winning

set_option autoImplicit false

open OnlineRandomization.Simulation in
theorem c03822b8_winsWithin_mono {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) :
    ∀ (k : ℕ) (r : List R) (a : List A), WinsWithin F α k r a →
      ∀ m : ℕ, k ≤ m → WinsWithin F α m r a := by
  intro k
  induction k with
  | zero =>
    intro r a h m _
    cases m with
    | zero => exact h
    | succ m => exact Or.inl h
  | succ k ih =>
    intro r a h m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rcases h with h | ⟨x, hx⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, fun y => ih _ _ (hx y) m (by omega)⟩

open OnlineRandomization.Simulation in
theorem solution {R A : Type*} [Fintype A] [Nonempty A]
    (F : Game R A) (α : ℝ → ℝ) (r : List R) (a : List A)
    (hlen : r.length = a.length) :
    IsWinning F α r a ↔
      (α (F.opt r) < F.cost r a ∨
        ∃ x : R, ∀ y : A, IsWinning F α (r ++ [x]) (a ++ [y])) := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => exact Or.inl hk
    | succ k =>
      rcases hk with h | ⟨x, hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨x, fun y => ⟨k, hx y⟩⟩
  · rintro (h | ⟨x, hx⟩)
    · exact ⟨0, h⟩
    · choose k hk using hx
      refine ⟨Finset.univ.sup k + 1, Or.inr ⟨x, fun y => ?_⟩⟩
      exact c03822b8_winsWithin_mono F α _ _ _ (hk y) _
        (Finset.le_sup (Finset.mem_univ y))
