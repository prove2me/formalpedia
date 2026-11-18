-- Prove2me | solution 1 for RealPinwheel.FiveSixths.covered_fragment_P9_0100
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:43:04.238132+00:00
-- url     : https://prove2.me/submissions/df7ccb62-7885-4c84-9f67-4ec1bc5aa91a

import Definitions.Def_RealPinwheel_FiveSixths_FragmentTreeP9_0100
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
theorem solution (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((upperAtom (⟨6, by decide⟩ : Fin 9) 1 12 false) :: (upperAtom (⟨3, by decide⟩ : Fin 9) 1 9 true) :: (complementAtom (upperAtom (⟨5, by decide⟩ : Fin 9) 1 12 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 2 17 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 1 8 true)) :: (upperAtom (⟨7, by decide⟩ : Fin 9) 1 12 true) :: (complementAtom (upperAtom (⟨7, by decide⟩ : Fin 9) 3 44 false)) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 29 297 false)) :: (complementAtom (upperAtom (⟨7, by decide⟩ : Fin 9) 1 20 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 3 20 false) :: (complementAtom (upperAtom (⟨6, by decide⟩ : Fin 9) 1 18 false)) :: (upperAtom (⟨1, by decide⟩ : Fin 9) 4 27 true) :: (complementAtom (upperAtom (⟨5, by decide⟩ : Fin 9) 1 18 false)) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 14 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 1 13 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 13 138 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 7 68 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by
  have hc : fragmentObligations 7968 codeFunctionP9 fragmentContextP9_0100 fragmentTreeP9_0100 := by
    unfold fragmentTreeP9_0100
    apply fragmentComputed_sound
    decide +kernel
  exact fragment_sound 7968 codeFunctionP9 fragmentContextP9_0100 fragmentTreeP9_0100 hc d hΓ
