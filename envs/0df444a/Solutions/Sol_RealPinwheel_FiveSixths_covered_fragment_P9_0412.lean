-- Prove2me | solution 1 for RealPinwheel.FiveSixths.covered_fragment_P9_0412
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:28:43.212948+00:00
-- url     : https://prove2.me/submissions/961aaed9-5a47-48de-99aa-1d41afa282ea

import Definitions.Def_RealPinwheel_FiveSixths_FragmentTreeP9_0412
import Theorems.Thm_RealPinwheel_FiveSixths_fragment_sound
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0284
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0285
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0288
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0289
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0290
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0291
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0323
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0324
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0357
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0358
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0359
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0360
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0376
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
theorem solution (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((upperAtom (⟨5, by decide⟩ : Fin 9) 2 25 true) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 1 8 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 4 27 true)) :: (complementAtom (upperAtom (⟨5, by decide⟩ : Fin 9) 1 18 false)) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 14 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 1 13 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 13 138 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 7 68 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by
  have hc : fragmentObligations 7968 codeFunctionP9 fragmentContextP9_0412 fragmentTreeP9_0412 := by
    unfold fragmentTreeP9_0412
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
                exact RealPinwheel.FiveSixths.covered_fragment_P9_0284
              ·
                exact RealPinwheel.FiveSixths.covered_fragment_P9_0285
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0288
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0289
        ·
          rw [fragmentObligations]
          refine ⟨by decide, ?_, ?_⟩
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0290
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0291
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
                        apply fragmentComputed_sound
                        decide +kernel
                      ·
                        apply fragmentComputed_sound
                        decide +kernel
      ·
        rw [fragmentObligations]
        refine ⟨by decide, ?_, ?_⟩
        ·
          exact RealPinwheel.FiveSixths.covered_fragment_P9_0323
        ·
          exact RealPinwheel.FiveSixths.covered_fragment_P9_0324
    ·
      rw [fragmentObligations]
      refine ⟨by decide, ?_, ?_⟩
      ·
        rw [fragmentObligations]
        refine ⟨by decide, ?_, ?_⟩
        ·
          exact RealPinwheel.FiveSixths.covered_fragment_P9_0360
        ·
          rw [fragmentObligations]
          refine ⟨by decide, ?_, ?_⟩
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0357
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0358
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0359
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
        exact RealPinwheel.FiveSixths.covered_fragment_P9_0376
  exact fragment_sound 7968 codeFunctionP9 fragmentContextP9_0412 fragmentTreeP9_0412 hc d hΓ
