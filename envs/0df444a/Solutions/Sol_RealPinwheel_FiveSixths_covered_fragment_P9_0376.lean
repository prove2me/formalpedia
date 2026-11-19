-- Prove2me | solution 1 for RealPinwheel.FiveSixths.covered_fragment_P9_0376
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:25:20.287072+00:00
-- url     : https://prove2.me/submissions/8220a129-a1af-435c-bd0f-1b30ea0bec55

import Definitions.Def_RealPinwheel_FiveSixths_FragmentTreeP9_0376
import Theorems.Thm_RealPinwheel_FiveSixths_fragment_sound
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0361
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0362
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0363
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0364
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0367
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0368
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0369
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0370
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0374
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0375
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
theorem solution (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 10 true)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 1 9 false)) :: (upperAtom (⟨5, by decide⟩ : Fin 9) 2 25 true) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 1 8 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 4 27 true)) :: (complementAtom (upperAtom (⟨5, by decide⟩ : Fin 9) 1 18 false)) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 14 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 1 13 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 13 138 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 7 68 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by
  have hc : fragmentObligations 7968 codeFunctionP9 fragmentContextP9_0376 fragmentTreeP9_0376 := by
    unfold fragmentTreeP9_0376
    rw [fragmentObligations]
    refine ⟨by decide, ?_, ?_⟩
    ·
      rw [fragmentObligations]
      refine ⟨by decide, ?_, ?_⟩
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
                              rw [fragmentObligations]
                              refine ⟨by decide, ?_, ?_⟩
                              ·
                                apply fragmentComputed_sound
                                decide +kernel
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
                            apply fragmentComputed_sound
                            decide +kernel
                          ·
                            rw [fragmentObligations]
                            refine ⟨by decide, ?_, ?_⟩
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
                            apply fragmentComputed_sound
                            decide +kernel
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
                          rw [fragmentObligations]
                          refine ⟨by decide, ?_, ?_⟩
                          ·
                            apply fragmentComputed_sound
                            decide +kernel
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
                          apply fragmentComputed_sound
                          decide +kernel
        ·
          rw [fragmentObligations]
          refine ⟨by decide, ?_, ?_⟩
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
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
                  rw [fragmentObligations]
                  refine ⟨by decide, ?_, ?_⟩
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
                        rw [fragmentObligations]
                        refine ⟨by decide, ?_, ?_⟩
                        ·
                          apply fragmentComputed_sound
                          decide +kernel
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
              apply fragmentComputed_sound
              decide +kernel
            ·
              rw [fragmentObligations]
              refine ⟨by decide, ?_, ?_⟩
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
                    apply fragmentComputed_sound
                    decide +kernel
              ·
                rw [fragmentObligations]
                refine ⟨by decide, ?_, ?_⟩
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
                    apply fragmentComputed_sound
                    decide +kernel
                ·
                  apply fragmentComputed_sound
                  decide +kernel
      ·
        rw [fragmentObligations]
        refine ⟨by decide, ?_, ?_⟩
        ·
          exact RealPinwheel.FiveSixths.covered_fragment_P9_0361
        ·
          exact RealPinwheel.FiveSixths.covered_fragment_P9_0362
    ·
      rw [fragmentObligations]
      refine ⟨by decide, ?_, ?_⟩
      ·
        rw [fragmentObligations]
        refine ⟨by decide, ?_, ?_⟩
        ·
          rw [fragmentObligations]
          refine ⟨by decide, ?_, ?_⟩
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
                              rw [fragmentObligations]
                              refine ⟨by decide, ?_, ?_⟩
                              ·
                                apply fragmentComputed_sound
                                decide +kernel
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
                              apply fragmentComputed_sound
                              decide +kernel
                      ·
                        rw [fragmentObligations]
                        refine ⟨by decide, ?_, ?_⟩
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
                              rw [fragmentObligations]
                              refine ⟨by decide, ?_, ?_⟩
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
                                        rw [fragmentObligations]
                                        refine ⟨by decide, ?_, ?_⟩
                                        ·
                                          apply fragmentComputed_sound
                                          decide +kernel
                                        ·
                                          apply fragmentComputed_sound
                                          decide +kernel
                                      ·
                                        apply fragmentComputed_sound
                                        decide +kernel
                                    ·
                                      apply fragmentComputed_sound
                                      decide +kernel
                                ·
                                  apply fragmentComputed_sound
                                  decide +kernel
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
                              rw [fragmentObligations]
                              refine ⟨by decide, ?_, ?_⟩
                              ·
                                apply fragmentComputed_sound
                                decide +kernel
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
                          apply fragmentComputed_sound
                          decide +kernel
                ·
                  rw [fragmentObligations]
                  refine ⟨by decide, ?_, ?_⟩
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
                        rw [fragmentObligations]
                        refine ⟨by decide, ?_, ?_⟩
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
                            rw [fragmentObligations]
                            refine ⟨by decide, ?_, ?_⟩
                            ·
                              apply fragmentComputed_sound
                              decide +kernel
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
                        apply fragmentComputed_sound
                        decide +kernel
              ·
                rw [fragmentObligations]
                refine ⟨by decide, ?_, ?_⟩
                ·
                  rw [fragmentObligations]
                  refine ⟨by decide, ?_, ?_⟩
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
                        rw [fragmentObligations]
                        refine ⟨by decide, ?_, ?_⟩
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
                              rw [fragmentObligations]
                              refine ⟨by decide, ?_, ?_⟩
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
                                        apply fragmentComputed_sound
                                        decide +kernel
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
                                    apply fragmentComputed_sound
                                    decide +kernel
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
                              rw [fragmentObligations]
                              refine ⟨by decide, ?_, ?_⟩
                              ·
                                apply fragmentComputed_sound
                                decide +kernel
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
                                        rw [fragmentObligations]
                                        refine ⟨by decide, ?_, ?_⟩
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
                                  apply fragmentComputed_sound
                                  decide +kernel
                                ·
                                  rw [fragmentObligations]
                                  refine ⟨by decide, ?_, ?_⟩
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
                                      apply fragmentComputed_sound
                                      decide +kernel
                              ·
                                rw [fragmentObligations]
                                refine ⟨by decide, ?_, ?_⟩
                                ·
                                  rw [fragmentObligations]
                                  refine ⟨by decide, ?_, ?_⟩
                                  ·
                                    rw [fragmentObligations]
                                    refine ⟨by decide, ?_, ?_⟩
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
                                          rw [fragmentObligations]
                                          refine ⟨by decide, ?_, ?_⟩
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
                                              apply fragmentComputed_sound
                                              decide +kernel
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
                                            apply fragmentComputed_sound
                                            decide +kernel
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
                                        rw [fragmentObligations]
                                        refine ⟨by decide, ?_, ?_⟩
                                        ·
                                          apply fragmentComputed_sound
                                          decide +kernel
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
                                        apply fragmentComputed_sound
                                        decide +kernel
                                ·
                                  rw [fragmentObligations]
                                  refine ⟨by decide, ?_, ?_⟩
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
                                          rw [fragmentObligations]
                                          refine ⟨by decide, ?_, ?_⟩
                                          ·
                                            apply fragmentComputed_sound
                                            decide +kernel
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
                                        apply fragmentComputed_sound
                                        decide +kernel
                        ·
                          rw [fragmentObligations]
                          refine ⟨by decide, ?_, ?_⟩
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
                                  apply fragmentComputed_sound
                                  decide +kernel
                          ·
                            rw [fragmentObligations]
                            refine ⟨by decide, ?_, ?_⟩
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
                                  apply fragmentComputed_sound
                                  decide +kernel
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
                              rw [fragmentObligations]
                              refine ⟨by decide, ?_, ?_⟩
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
                                    apply fragmentComputed_sound
                                    decide +kernel
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
                              apply fragmentComputed_sound
                              decide +kernel
                  ·
                    rw [fragmentObligations]
                    refine ⟨by decide, ?_, ?_⟩
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
                          apply fragmentComputed_sound
                          decide +kernel
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
                          apply fragmentComputed_sound
                          decide +kernel
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
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0363
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0364
        ·
          rw [fragmentObligations]
          refine ⟨by decide, ?_, ?_⟩
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0368
            ·
              rw [fragmentObligations]
              refine ⟨by decide, ?_, ?_⟩
              ·
                exact RealPinwheel.FiveSixths.covered_fragment_P9_0367
              ·
                rw [fragmentObligations]
                refine ⟨by decide, ?_, ?_⟩
                ·
                  rw [fragmentObligations]
                  refine ⟨by decide, ?_, ?_⟩
                  ·
                    rw [fragmentObligations]
                    refine ⟨by decide, ?_, ?_⟩
                    ·
                      rw [fragmentObligations]
                      refine ⟨by decide, ?_, ?_⟩
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
                            rw [fragmentObligations]
                            refine ⟨by decide, ?_, ?_⟩
                            ·
                              apply fragmentComputed_sound
                              decide +kernel
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
                                apply fragmentComputed_sound
                                decide +kernel
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
                            apply fragmentComputed_sound
                            decide +kernel
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
                          apply fragmentComputed_sound
                          decide +kernel
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
                        apply fragmentComputed_sound
                        decide +kernel
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
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0369
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0370
      ·
        rw [fragmentObligations]
        refine ⟨by decide, ?_, ?_⟩
        ·
          exact RealPinwheel.FiveSixths.covered_fragment_P9_0374
        ·
          exact RealPinwheel.FiveSixths.covered_fragment_P9_0375
  exact fragment_sound 7968 codeFunctionP9 fragmentContextP9_0376 fragmentTreeP9_0376 hc d hΓ
