-- Prove2me | solution 1 for RealPinwheel.FiveSixths.covered_fragment_D8_0167
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:03:36.318782+00:00
-- url     : https://prove2.me/submissions/e2aaabe4-ccc2-4ef9-af26-16936dda0638

import Definitions.Def_RealPinwheel_FiveSixths_FragmentTreeD8_0167
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
theorem solution (d : Fin 8 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨4, by decide⟩ : Fin 8) 9 256 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 8) 2 19 true)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 8) 1 6 true)) :: (upperAtom (⟨1, by decide⟩ : Fin 8) 2 9 false) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 8) 1 16 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 8) 3 16 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 8) 2 15 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 8) 2 27 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 8) 1 8 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 8) 1 3 true) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 1 4 true)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 2 15 false)) :: initialAtoms 8 8 : List (LinearAtom 8)), a.Holds d) :
    ∃ j : Fin 3725, codeBox (codeFunctionD8 j.val) d := by
  have hc : fragmentObligations 3725 codeFunctionD8 fragmentContextD8_0167 fragmentTreeD8_0167 := by
    unfold fragmentTreeD8_0167
    apply fragmentComputed_sound
    decide +kernel
  exact fragment_sound 3725 codeFunctionD8 fragmentContextD8_0167 fragmentTreeD8_0167 hc d hΓ
