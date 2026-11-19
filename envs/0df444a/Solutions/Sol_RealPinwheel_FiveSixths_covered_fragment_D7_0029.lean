-- Prove2me | solution 1 for RealPinwheel.FiveSixths.covered_fragment_D7_0029
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:19:09.472318+00:00
-- url     : https://prove2.me/submissions/67805536-bc90-43a4-887f-f8e9d3c389b8

import Definitions.Def_RealPinwheel_FiveSixths_FragmentTreeD7_0029
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
theorem solution (d : Fin 7 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨1, by decide⟩ : Fin 7) 3 16 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 7) 1 3 false)) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 7) 1 21 true)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 7) 1 14 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 7) 1 13 false)) :: (upperAtom (⟨1, by decide⟩ : Fin 7) 3 13 false) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 7) 1 6 true)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 7) 1 10 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 7) 2 5 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 7) 3 10 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 7) 2 11 false)) :: initialAtoms 7 7 : List (LinearAtom 7)), a.Holds d) :
    ∃ j : Fin 1657, codeBox (codeFunctionD7 j.val) d := by
  have hc : fragmentObligations 1657 codeFunctionD7 fragmentContextD7_0029 fragmentTreeD7_0029 := by
    unfold fragmentTreeD7_0029
    apply fragmentComputed_sound
    decide +kernel
  exact fragment_sound 1657 codeFunctionD7 fragmentContextD7_0029 fragmentTreeD7_0029 hc d hΓ
