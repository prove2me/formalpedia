-- Prove2me | solution 1 for RealPinwheel.FiveSixths.covered_fragment_P9_0464
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:44:57.04822+00:00
-- url     : https://prove2.me/submissions/80bf51c1-66f3-4f97-9a6d-802e6f70c6a8

import Definitions.Def_RealPinwheel_FiveSixths_FragmentTreeP9_0464
import Theorems.Thm_RealPinwheel_FiveSixths_fragment_sound
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0442
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0443
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0444
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0446
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0447
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0448
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0449
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0450
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0451
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0452
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0453
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0454
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0455
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0456
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0457
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
theorem solution (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((upperAtom (⟨4, by decide⟩ : Fin 9) 7 72 false) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 5 38 false)) :: (upperAtom (⟨5, by decide⟩ : Fin 9) 9 152 false) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 18 false)) :: (upperAtom (⟨1, by decide⟩ : Fin 9) 1 6 true) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 23 336 false)) :: (upperAtom (⟨2, by decide⟩ : Fin 9) 23 168 false) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 1 11 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 2 21 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 2 7 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by
  have hc : fragmentObligations 7968 codeFunctionP9 fragmentContextP9_0464 fragmentTreeP9_0464 := by
    unfold fragmentTreeP9_0464
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
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0442
        ·
          rw [fragmentObligations]
          refine ⟨by decide, ?_, ?_⟩
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0443
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0444
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0446
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0447
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
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0448
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0449
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0450
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0451
        ·
          rw [fragmentObligations]
          refine ⟨by decide, ?_, ?_⟩
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0452
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0453
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              rw [fragmentObligations]
              refine ⟨by decide, ?_, ?_⟩
              ·
                exact RealPinwheel.FiveSixths.covered_fragment_P9_0454
              ·
                exact RealPinwheel.FiveSixths.covered_fragment_P9_0455
            ·
              rw [fragmentObligations]
              refine ⟨by decide, ?_, ?_⟩
              ·
                exact RealPinwheel.FiveSixths.covered_fragment_P9_0456
              ·
                exact RealPinwheel.FiveSixths.covered_fragment_P9_0457
  exact fragment_sound 7968 codeFunctionP9 fragmentContextP9_0464 fragmentTreeP9_0464 hc d hΓ
