-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_small_012
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:38:25.66302+00:00
-- url     : https://prove2.me/submissions/52fa6b2d-4d6e-408d-a0bc-650485ce9567

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_240
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_241
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_242
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_243
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_244
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_245
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_246
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_247
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_248
open RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private lemma of_witness {n : ℕ} (A : Instance n) (w : CycleWitness n) (M : ℕ)
    (hc : witnessCheck w = true) (hl : w.length ≤ M)
    (hb : codeBox w.code (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin n), 0 < L ∧ L ≤ M ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  obtain ⟨L, S, hL, hp, hv⟩ := witnessCheck_sound A.positive_dimension w hc A.period
    (fun i => lt_of_lt_of_le (by norm_num) (A.one_le i)) hb
  exact ⟨L, S, hp.1, hL ▸ hl, hp.2, hv⟩

theorem solution (A : Instance 8) (j : Fin 3725)
    (hlo : 3331 ≤ j.val) (hhi : j.val < 3725)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 36, codeFunctionD8 (3331 + i.val) = (witnessD8_240 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 38, codeFunctionD8 (3367 + i.val) = (witnessD8_241 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 38, codeFunctionD8 (3405 + i.val) = (witnessD8_242 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 41, codeFunctionD8 (3443 + i.val) = (witnessD8_243 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 44, codeFunctionD8 (3484 + i.val) = (witnessD8_244 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 48, codeFunctionD8 (3528 + i.val) = (witnessD8_245 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 51, codeFunctionD8 (3576 + i.val) = (witnessD8_246 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 57, codeFunctionD8 (3627 + i.val) = (witnessD8_247 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 41, codeFunctionD8 (3684 + i.val) = (witnessD8_248 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_9 : j.val < 3484
  ·
    by_cases h0_4 : j.val < 3405
    ·
      by_cases h0_2 : j.val < 3367
      ·
        let i : Fin 36 := ⟨j.val - 3331, by omega⟩
        apply of_witness A (witnessD8_240 i) 608 (RealPinwheel.FiveSixths.checked_D8_240 i).1 (RealPinwheel.FiveSixths.checked_D8_240 i).2
        rw [← align_0 i]
        have he : 3331 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
      ·
        let i : Fin 38 := ⟨j.val - 3367, by omega⟩
        apply of_witness A (witnessD8_241 i) 608 (RealPinwheel.FiveSixths.checked_D8_241 i).1 (RealPinwheel.FiveSixths.checked_D8_241 i).2
        rw [← align_1 i]
        have he : 3367 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
    ·
      by_cases h2_4 : j.val < 3443
      ·
        let i : Fin 38 := ⟨j.val - 3405, by omega⟩
        apply of_witness A (witnessD8_242 i) 608 (RealPinwheel.FiveSixths.checked_D8_242 i).1 (RealPinwheel.FiveSixths.checked_D8_242 i).2
        rw [← align_2 i]
        have he : 3405 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
      ·
        let i : Fin 41 := ⟨j.val - 3443, by omega⟩
        apply of_witness A (witnessD8_243 i) 608 (RealPinwheel.FiveSixths.checked_D8_243 i).1 (RealPinwheel.FiveSixths.checked_D8_243 i).2
        rw [← align_3 i]
        have he : 3443 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
  ·
    by_cases h4_9 : j.val < 3576
    ·
      by_cases h4_6 : j.val < 3528
      ·
        let i : Fin 44 := ⟨j.val - 3484, by omega⟩
        apply of_witness A (witnessD8_244 i) 608 (RealPinwheel.FiveSixths.checked_D8_244 i).1 (RealPinwheel.FiveSixths.checked_D8_244 i).2
        rw [← align_4 i]
        have he : 3484 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
      ·
        let i : Fin 48 := ⟨j.val - 3528, by omega⟩
        apply of_witness A (witnessD8_245 i) 608 (RealPinwheel.FiveSixths.checked_D8_245 i).1 (RealPinwheel.FiveSixths.checked_D8_245 i).2
        rw [← align_5 i]
        have he : 3528 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
    ·
      by_cases h6_9 : j.val < 3627
      ·
        let i : Fin 51 := ⟨j.val - 3576, by omega⟩
        apply of_witness A (witnessD8_246 i) 608 (RealPinwheel.FiveSixths.checked_D8_246 i).1 (RealPinwheel.FiveSixths.checked_D8_246 i).2
        rw [← align_6 i]
        have he : 3576 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
      ·
        by_cases h7_9 : j.val < 3684
        ·
          let i : Fin 57 := ⟨j.val - 3627, by omega⟩
          apply of_witness A (witnessD8_247 i) 608 (RealPinwheel.FiveSixths.checked_D8_247 i).1 (RealPinwheel.FiveSixths.checked_D8_247 i).2
          rw [← align_7 i]
          have he : 3627 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 41 := ⟨j.val - 3684, by omega⟩
          apply of_witness A (witnessD8_248 i) 608 (RealPinwheel.FiveSixths.checked_D8_248 i).1 (RealPinwheel.FiveSixths.checked_D8_248 i).2
          rw [← align_8 i]
          have he : 3684 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
