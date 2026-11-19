-- Prove2me | solution 1 for RealPinwheel.FiveSixths.covered_fragment_D8_0205
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:40:39.845046+00:00
-- url     : https://prove2.me/submissions/7a1bf7df-fa7b-483f-ba0d-15c9342ba615

import Definitions.Def_RealPinwheel_FiveSixths_FragmentTreeD8_0205
import Theorems.Thm_RealPinwheel_FiveSixths_fragment_sound
open RealPinwheel.FiveSixths
private def fragmentComputed {n : ℕ} (N : ℕ) (codes : ℕ → CycleCode)
    (Γ : List (LinearAtom n)) : LinearFragment n → Bool
  | .empty c => combinationCheck Γ c (falseAtom n)
  | .word j cs => linearCoverCheck N codes Γ (.word j cs)
  | .split i p q st l r => decide (0 < q) &&
      fragmentComputed N codes (upperAtom i p q st :: Γ) l &&
      fragmentComputed N codes (complementAtom (upperAtom i p q st) :: Γ) r
  | .hole => false
private theorem fragmentComputed_sound {n : ℕ} (N : ℕ) (codes : ℕ → CycleCode)
    (Γ : List (LinearAtom n)) (tree : LinearFragment n)
    (h : fragmentComputed N codes Γ tree = true) : fragmentObligations N codes Γ tree := by
  induction tree generalizing Γ with
  | empty c => exact h
  | word j cs => exact h
  | hole => simp [fragmentComputed] at h
  | split i p q st l r ihl ihr =>
    simp only [fragmentComputed, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, ihl _ h.1.2, ihr _ h.2⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution (d : Fin 8 → ℝ) (hΓ : ∀ a ∈ ((upperAtom (⟨1, by decide⟩ : Fin 8) 3 14 false) :: (upperAtom (⟨4, by decide⟩ : Fin 8) 1 14 false) :: (upperAtom (⟨0, by decide⟩ : Fin 8) 5 14 false) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 8) 1 26 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 8) 1 16 false)) :: (upperAtom (⟨1, by decide⟩ : Fin 8) 1 4 false) :: (upperAtom (⟨2, by decide⟩ : Fin 8) 1 8 false) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 8) 3 17 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 8) 2 15 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 8) 3 44 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 8) 3 35 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 8) 3 7 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 1 3 true)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 1 4 true)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 2 15 false)) :: initialAtoms 8 8 : List (LinearAtom 8)), a.Holds d) :
    ∃ j : Fin 3725, codeBox (codeFunctionD8 j.val) d := by
  have hc : fragmentObligations 3725 codeFunctionD8 fragmentContextD8_0205 fragmentTreeD8_0205 := by
    unfold fragmentTreeD8_0205
    apply fragmentComputed_sound
    decide +kernel
  exact fragment_sound 3725 codeFunctionD8 fragmentContextD8_0205 fragmentTreeD8_0205 hc d hΓ
