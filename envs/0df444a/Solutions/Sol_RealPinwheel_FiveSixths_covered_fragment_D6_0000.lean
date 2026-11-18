-- Prove2me | solution 1 for RealPinwheel.FiveSixths.covered_fragment_D6_0000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:50:04.397864+00:00
-- url     : https://prove2.me/submissions/8e7ebd2d-8690-44cc-baef-fa3cd5a7cb11

import Definitions.Def_RealPinwheel_FiveSixths_FragmentTreeD6_0000
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
theorem solution (d : Fin 6 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨4, by decide⟩ : Fin 6) 1 16 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 6) 1 10 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 6) 1 4 false) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 6) 1 9 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 6) 2 15 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 6) 1 3 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 6) 2 11 false)) :: initialAtoms 6 6 : List (LinearAtom 6)), a.Holds d) :
    ∃ j : Fin 630, codeBox (codeFunctionD6 j.val) d := by
  have hc : fragmentObligations 630 codeFunctionD6 fragmentContextD6_0000 fragmentTreeD6_0000 := by
    unfold fragmentTreeD6_0000
    apply fragmentComputed_sound
    decide +kernel
  exact fragment_sound 630 codeFunctionD6 fragmentContextD6_0000 fragmentTreeD6_0000 hc d hΓ
