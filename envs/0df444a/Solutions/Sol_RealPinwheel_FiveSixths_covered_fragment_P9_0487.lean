-- Prove2me | solution 1 for RealPinwheel.FiveSixths.covered_fragment_P9_0487
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:51:01.690449+00:00
-- url     : https://prove2.me/submissions/5a12a75f-6eac-4505-87c9-24db7fef7e67

import Definitions.Def_RealPinwheel_FiveSixths_FragmentTreeP9_0487
import Theorems.Thm_RealPinwheel_FiveSixths_fragment_sound
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0474
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0475
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0480
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0481
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0484
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0485
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
theorem solution (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 1 4 true)) :: (upperAtom (⟨4, by decide⟩ : Fin 9) 1 10 false) :: (upperAtom (⟨6, by decide⟩ : Fin 9) 1 20 false) :: (complementAtom (upperAtom (⟨5, by decide⟩ : Fin 9) 9 152 false)) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 18 false)) :: (upperAtom (⟨1, by decide⟩ : Fin 9) 1 6 true) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 23 336 false)) :: (upperAtom (⟨2, by decide⟩ : Fin 9) 23 168 false) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 1 11 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 2 21 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 2 7 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by
  have hc : fragmentObligations 7968 codeFunctionP9 fragmentContextP9_0487 fragmentTreeP9_0487 := by
    unfold fragmentTreeP9_0487
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
                                apply fragmentComputed_sound
                                decide +kernel
                              ·
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
                                  apply fragmentComputed_sound
                                  decide +kernel
                              ·
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
                              apply fragmentComputed_sound
                              decide +kernel
                          ·
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
                                apply fragmentComputed_sound
                                decide +kernel
                            ·
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
                          apply fragmentComputed_sound
                          decide +kernel
                        ·
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
                                apply fragmentComputed_sound
                                decide +kernel
                            ·
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
            exact RealPinwheel.FiveSixths.covered_fragment_P9_0474
          ·
            exact RealPinwheel.FiveSixths.covered_fragment_P9_0475
    ·
      rw [fragmentObligations]
      refine ⟨by decide, ?_, ?_⟩
      ·
        exact RealPinwheel.FiveSixths.covered_fragment_P9_0485
      ·
        rw [fragmentObligations]
        refine ⟨by decide, ?_, ?_⟩
        ·
          rw [fragmentObligations]
          refine ⟨by decide, ?_, ?_⟩
          ·
            exact RealPinwheel.FiveSixths.covered_fragment_P9_0480
          ·
            exact RealPinwheel.FiveSixths.covered_fragment_P9_0481
        ·
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
                          apply fragmentComputed_sound
                          decide +kernel
                        ·
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
                    rw [fragmentObligations]
                    refine ⟨by decide, ?_, ?_⟩
                    ·
                      apply fragmentComputed_sound
                      decide +kernel
                    ·
                      apply fragmentComputed_sound
                      decide +kernel
          ·
            exact RealPinwheel.FiveSixths.covered_fragment_P9_0484
  exact fragment_sound 7968 codeFunctionP9 fragmentContextP9_0487 fragmentTreeP9_0487 hc d hΓ
