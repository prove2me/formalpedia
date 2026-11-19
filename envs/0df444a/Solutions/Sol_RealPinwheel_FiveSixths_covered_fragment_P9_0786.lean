-- Prove2me | solution 1 for RealPinwheel.FiveSixths.covered_fragment_P9_0786
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:48:55.854254+00:00
-- url     : https://prove2.me/submissions/14494b1e-409d-4b97-9a4d-c67a22772f2c

import Definitions.Def_RealPinwheel_FiveSixths_FragmentTreeP9_0786
import Theorems.Thm_RealPinwheel_FiveSixths_fragment_sound
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0725
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0726
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0727
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0728
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0735
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0736
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0737
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0738
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0745
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0746
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0747
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0748
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0752
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0753
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0767
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0768
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0775
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0776
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0779
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0780
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0781
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0782
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0783
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0784
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
theorem solution (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 18 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 1 6 true)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 23 336 false)) :: (upperAtom (⟨2, by decide⟩ : Fin 9) 23 168 false) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 1 11 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 2 21 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 2 7 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by
  have hc : fragmentObligations 7968 codeFunctionP9 fragmentContextP9_0786 fragmentTreeP9_0786 := by
    unfold fragmentTreeP9_0786
    rw [fragmentObligations]
    refine ⟨by decide, ?_, ?_⟩
    ·
      rw [fragmentObligations]
      refine ⟨by decide, ?_, ?_⟩
      ·
        exact RealPinwheel.FiveSixths.covered_fragment_P9_0725
      ·
        exact RealPinwheel.FiveSixths.covered_fragment_P9_0726
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
                  exact RealPinwheel.FiveSixths.covered_fragment_P9_0727
                ·
                  exact RealPinwheel.FiveSixths.covered_fragment_P9_0728
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
                        apply fragmentComputed_sound
                        decide +kernel
                    ·
                      apply fragmentComputed_sound
                      decide +kernel
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0735
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0736
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
                        exact RealPinwheel.FiveSixths.covered_fragment_P9_0737
                      ·
                        exact RealPinwheel.FiveSixths.covered_fragment_P9_0738
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
                  exact RealPinwheel.FiveSixths.covered_fragment_P9_0745
                ·
                  exact RealPinwheel.FiveSixths.covered_fragment_P9_0746
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
                    exact RealPinwheel.FiveSixths.covered_fragment_P9_0747
                  ·
                    exact RealPinwheel.FiveSixths.covered_fragment_P9_0748
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
                        apply fragmentComputed_sound
                        decide +kernel
                    ·
                      apply fragmentComputed_sound
                      decide +kernel
              ·
                rw [fragmentObligations]
                refine ⟨by decide, ?_, ?_⟩
                ·
                  exact RealPinwheel.FiveSixths.covered_fragment_P9_0752
                ·
                  exact RealPinwheel.FiveSixths.covered_fragment_P9_0753
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0767
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0768
        ·
          rw [fragmentObligations]
          refine ⟨by decide, ?_, ?_⟩
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0775
            ·
              exact RealPinwheel.FiveSixths.covered_fragment_P9_0776
          ·
            rw [fragmentObligations]
            refine ⟨by decide, ?_, ?_⟩
            ·
              rw [fragmentObligations]
              refine ⟨by decide, ?_, ?_⟩
              ·
                exact RealPinwheel.FiveSixths.covered_fragment_P9_0779
              ·
                exact RealPinwheel.FiveSixths.covered_fragment_P9_0780
            ·
              rw [fragmentObligations]
              refine ⟨by decide, ?_, ?_⟩
              ·
                rw [fragmentObligations]
                refine ⟨by decide, ?_, ?_⟩
                ·
                  exact RealPinwheel.FiveSixths.covered_fragment_P9_0781
                ·
                  exact RealPinwheel.FiveSixths.covered_fragment_P9_0782
              ·
                rw [fragmentObligations]
                refine ⟨by decide, ?_, ?_⟩
                ·
                  exact RealPinwheel.FiveSixths.covered_fragment_P9_0783
                ·
                  exact RealPinwheel.FiveSixths.covered_fragment_P9_0784
  exact fragment_sound 7968 codeFunctionP9 fragmentContextP9_0786 fragmentTreeP9_0786 hc d hΓ
