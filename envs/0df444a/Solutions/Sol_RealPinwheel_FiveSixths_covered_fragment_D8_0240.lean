-- Prove2me | solution 1 for RealPinwheel.FiveSixths.covered_fragment_D8_0240
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:54:15.631211+00:00
-- url     : https://prove2.me/submissions/bfef719e-3a37-4e32-a1bb-4e74639508d6

import Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_fragment_sound
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D8_0084
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D8_0085
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D8_0238
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D8_0239
namespace RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def fragmentContextD8_0240 : List (LinearAtom 8) := initialAtoms 8 8
def fragmentTreeD8_0240 : LinearFragment 8 :=
 
  (.split ⟨0, by decide⟩ 2 15 false
  (.split ⟨6, by decide⟩ 1 10 false
  (.word 3235 ![⟨1, [(1, 1)]⟩, ⟨1, [(10, 15), (1, 1)]⟩, ⟨1, [(10, 15), (11, 15), (1, 1)]⟩, ⟨1, [(10, 15), (11, 15), (12, 15), (1, 1)]⟩, ⟨1, [(10, 15), (11, 15), (12, 15), (13, 15), (1, 1)]⟩, ⟨1, [(10, 15), (11, 15), (12, 15), (13, 15), (14, 15), (1, 1)]⟩, ⟨1, [(0, 1)]⟩, ⟨1, [(16, 10), (0, 1)]⟩])
  (.split ⟨3, by decide⟩ 1 8 false
  (.split ⟨7, by decide⟩ 1 12 false
  (.word 1053 ![⟨15, [(3, 22)]⟩, ⟨15, [(12, 330), (3, 22)]⟩, ⟨15, [(12, 330), (13, 330), (3, 22)]⟩, ⟨1, [(1, 1)]⟩, ⟨1, [(15, 8), (1, 1)]⟩, ⟨45, [(11, 60), (12, 60), (13, 120), (14, 180), (15, 240), (16, 300), (19, 10), (2, 6)]⟩, ⟨21, [(11, 24), (12, 24), (13, 48), (14, 72), (15, 96), (16, 120), (17, 144), (19, 4)]⟩, ⟨1, [(0, 1)]⟩])
  (.word 2864 ![⟨15, [(3, 7)]⟩, ⟨24, [(12, 84), (14, 84), (15, 168), (16, 252), (17, 336), (19, 14), (2, 42), (0, 7)]⟩, ⟨180, [(12, 420), (13, 840), (15, 420), (16, 840), (17, 1260), (19, 70), (2, 168), (0, 35)]⟩, ⟨48, [(12, 420), (13, 840), (14, 1260), (16, 420), (17, 840), (19, 70), (2, 126), (0, 35)]⟩, ⟨60, [(12, 420), (13, 840), (14, 1260), (15, 1680), (17, 420), (19, 70), (2, 84), (0, 35)]⟩, ⟨72, [(12, 420), (13, 840), (14, 1260), (15, 1680), (16, 2100), (19, 70), (2, 42), (0, 35)]⟩, ⟨12, [(12, 60), (13, 120), (14, 180), (15, 240), (16, 300), (17, 360), (19, 10), (0, 5)]⟩, ⟨48, [(12, 210), (13, 420), (14, 630), (15, 840), (16, 1050), (17, 1260), (18, 1470), (19, 35)]⟩]))
  (.split ⟨1, by decide⟩ 9 68 false
  (.word 1171 ![⟨15, [(3, 17)]⟩, ⟨1, [(0, 1)]⟩, ⟨1, [(13, 68), (0, 1)]⟩, ⟨1, [(13, 68), (14, 68), (0, 1)]⟩, ⟨75, [(11, 1020), (12, 1020), (13, 2040), (14, 3060), (15, 4080), (17, 1020), (19, 170), (2, 204)]⟩, ⟨60, [(11, 510), (12, 510), (13, 1020), (14, 1530), (16, 510), (19, 85), (2, 51), (1, 255)]⟩, ⟨2, [(11, 6), (12, 6), (13, 12), (14, 18), (16, 6), (17, 12), (19, 1), (1, 3)]⟩, ⟨30, [(12, 510), (13, 1020), (14, 1530), (16, 510), (17, 1020), (19, 85), (2, 153), (1, 255)]⟩])
  (.split ⟨4, by decide⟩ 2 17 false
  (.word 2993 ![⟨15, [(4, 34)]⟩, ⟨15, [(13, 510), (4, 34)]⟩, ⟨15, [(13, 105), (14, 105), (4, 7)]⟩, ⟨120, [(12, 210), (13, 210), (14, 420), (15, 630), (17, 210), (18, 420), (20, 35), (3, 63)]⟩, ⟨1, [(0, 1)]⟩, ⟨120, [(12, 1020), (13, 1020), (15, 1020), (17, 1020), (20, 170), (3, 102), (2, 255), (1, 30)]⟩, ⟨36, [(12, 204), (13, 204), (15, 204), (17, 204), (18, 408), (20, 34), (2, 51), (1, 6)]⟩, ⟨60, [(13, 1020), (15, 1020), (17, 1020), (18, 2040), (20, 170), (3, 306), (2, 255), (1, 30)]⟩])
  (.word 2659 ![⟨1020, [(12, 19380), (15, 19380), (18, 19380), (20, 3230), (3, 3876), (2, 4845), (1, 285), (0, 1140)]⟩, ⟨2040, [(12, 13260), (13, 13260), (15, 13260), (18, 13260), (20, 2210), (3, 2652), (2, 3315), (0, 780)]⟩, ⟨2040, [(12, 26520), (13, 26520), (18, 26520), (20, 4420), (3, 5304), (2, 3315), (1, 780), (0, 1560)]⟩, ⟨510, [(12, 9690), (13, 9690), (15, 9690), (18, 9690), (20, 1615), (3, 1938), (1, 285), (0, 570)]⟩, ⟨510, [(12, 19380), (13, 19380), (15, 19380), (18, 19380), (20, 3230), (3, 3876), (2, 4845), (1, 570)]⟩, ⟨1020, [(12, 19380), (13, 19380), (15, 19380), (20, 3230), (3, 1938), (2, 4845), (1, 570), (0, 1140)]⟩, ⟨408, [(12, 3876), (13, 3876), (15, 3876), (18, 3876), (20, 646), (2, 969), (1, 114), (0, 228)]⟩, ⟨1020, [(13, 19380), (15, 19380), (18, 19380), (20, 3230), (3, 3876), (2, 4845), (1, 570), (0, 1140)]⟩])))))
  (.split ⟨0, by decide⟩ 1 4 true
  (.split ⟨1, by decide⟩ 1 8 false (.hole) (.hole))
  (.split ⟨0, by decide⟩ 1 3 true (.hole) (.hole))))
end RealPinwheel.FiveSixths
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
theorem solution (d : Fin 8 → ℝ) (hΓ : ∀ a ∈ (initialAtoms 8 8 : List (LinearAtom 8)), a.Holds d) :
    ∃ j : Fin 3725, codeBox (codeFunctionD8 j.val) d := by
  have hc : fragmentObligations 3725 codeFunctionD8 fragmentContextD8_0240 fragmentTreeD8_0240 := by
    unfold fragmentTreeD8_0240
    rw [fragmentObligations]
    refine ⟨by decide, ?_, ?_⟩
    ·
      rw [fragmentObligations]
      refine ⟨by decide, ?_, ?_⟩
      ·
        apply fragmentComputed_sound
        decide +kernel
      ·
        rw [fragmentObligations]
        refine ⟨by decide, ?_, ?_⟩
        ·
          rw [fragmentObligations]
          refine ⟨by decide, ?_, ?_⟩
          ·
            apply fragmentComputed_sound
            decide +kernel
          ·
            apply fragmentComputed_sound
            decide +kernel
        ·
          rw [fragmentObligations]
          refine ⟨by decide, ?_, ?_⟩
          ·
            apply fragmentComputed_sound
            decide +kernel
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              apply fragmentComputed_sound
              decide +kernel
            ·
              apply fragmentComputed_sound
              decide +kernel
    ·
      rw [fragmentObligations]
      refine ⟨by decide, ?_, ?_⟩
      ·
        rw [fragmentObligations]
        refine ⟨by decide, ?_, ?_⟩
        ·
          exact RealPinwheel.FiveSixths.covered_fragment_D8_0084
        ·
          exact RealPinwheel.FiveSixths.covered_fragment_D8_0085
      ·
        rw [fragmentObligations]
        refine ⟨by decide, ?_, ?_⟩
        ·
          exact RealPinwheel.FiveSixths.covered_fragment_D8_0238
        ·
          exact RealPinwheel.FiveSixths.covered_fragment_D8_0239
  exact fragment_sound 3725 codeFunctionD8 fragmentContextD8_0240 fragmentTreeD8_0240 hc d hΓ
