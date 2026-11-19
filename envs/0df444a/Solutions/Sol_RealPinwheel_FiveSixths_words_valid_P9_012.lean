-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_012
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:07:56.758496+00:00
-- url     : https://prove2.me/submissions/4490e2d6-6a56-479c-a815-03636d155c5c

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_240
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_241
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_242
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_243
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_244
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_245
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_246
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_247
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_248
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_249
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_250
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_251
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_252
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_253
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_254
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_255
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_256
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_257
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_258
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_259
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

theorem solution (A : Instance 9) (j : Fin 7968)
    (hlo : 3108 ≤ j.val) (hhi : j.val < 3756)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 30, codeFunctionP9 (3108 + i.val) = (witnessP9_240 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 31, codeFunctionP9 (3138 + i.val) = (witnessP9_241 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 31, codeFunctionP9 (3169 + i.val) = (witnessP9_242 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 31, codeFunctionP9 (3200 + i.val) = (witnessP9_243 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 31, codeFunctionP9 (3231 + i.val) = (witnessP9_244 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 31, codeFunctionP9 (3262 + i.val) = (witnessP9_245 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 31, codeFunctionP9 (3293 + i.val) = (witnessP9_246 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 31, codeFunctionP9 (3324 + i.val) = (witnessP9_247 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 32, codeFunctionP9 (3355 + i.val) = (witnessP9_248 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 32, codeFunctionP9 (3387 + i.val) = (witnessP9_249 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 33, codeFunctionP9 (3419 + i.val) = (witnessP9_250 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 33, codeFunctionP9 (3452 + i.val) = (witnessP9_251 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 33, codeFunctionP9 (3485 + i.val) = (witnessP9_252 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 33, codeFunctionP9 (3518 + i.val) = (witnessP9_253 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 34, codeFunctionP9 (3551 + i.val) = (witnessP9_254 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 34, codeFunctionP9 (3585 + i.val) = (witnessP9_255 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 34, codeFunctionP9 (3619 + i.val) = (witnessP9_256 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 34, codeFunctionP9 (3653 + i.val) = (witnessP9_257 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 34, codeFunctionP9 (3687 + i.val) = (witnessP9_258 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 35, codeFunctionP9 (3721 + i.val) = (witnessP9_259 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 3419
  ·
    by_cases h0_10 : j.val < 3262
    ·
      by_cases h0_5 : j.val < 3169
      ·
        by_cases h0_2 : j.val < 3138
        ·
          let i : Fin 30 := ⟨j.val - 3108, by omega⟩
          apply of_witness A (witnessP9_240 i) 1800 (RealPinwheel.FiveSixths.checked_P9_240 i).1 (RealPinwheel.FiveSixths.checked_P9_240 i).2
          rw [← align_0 i]
          have he : 3108 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 31 := ⟨j.val - 3138, by omega⟩
          apply of_witness A (witnessP9_241 i) 1800 (RealPinwheel.FiveSixths.checked_P9_241 i).1 (RealPinwheel.FiveSixths.checked_P9_241 i).2
          rw [← align_1 i]
          have he : 3138 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 3200
        ·
          let i : Fin 31 := ⟨j.val - 3169, by omega⟩
          apply of_witness A (witnessP9_242 i) 1800 (RealPinwheel.FiveSixths.checked_P9_242 i).1 (RealPinwheel.FiveSixths.checked_P9_242 i).2
          rw [← align_2 i]
          have he : 3169 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 3231
          ·
            let i : Fin 31 := ⟨j.val - 3200, by omega⟩
            apply of_witness A (witnessP9_243 i) 1800 (RealPinwheel.FiveSixths.checked_P9_243 i).1 (RealPinwheel.FiveSixths.checked_P9_243 i).2
            rw [← align_3 i]
            have he : 3200 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 31 := ⟨j.val - 3231, by omega⟩
            apply of_witness A (witnessP9_244 i) 1800 (RealPinwheel.FiveSixths.checked_P9_244 i).1 (RealPinwheel.FiveSixths.checked_P9_244 i).2
            rw [← align_4 i]
            have he : 3231 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 3324
      ·
        by_cases h5_7 : j.val < 3293
        ·
          let i : Fin 31 := ⟨j.val - 3262, by omega⟩
          apply of_witness A (witnessP9_245 i) 1800 (RealPinwheel.FiveSixths.checked_P9_245 i).1 (RealPinwheel.FiveSixths.checked_P9_245 i).2
          rw [← align_5 i]
          have he : 3262 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 31 := ⟨j.val - 3293, by omega⟩
          apply of_witness A (witnessP9_246 i) 1800 (RealPinwheel.FiveSixths.checked_P9_246 i).1 (RealPinwheel.FiveSixths.checked_P9_246 i).2
          rw [← align_6 i]
          have he : 3293 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 3355
        ·
          let i : Fin 31 := ⟨j.val - 3324, by omega⟩
          apply of_witness A (witnessP9_247 i) 1800 (RealPinwheel.FiveSixths.checked_P9_247 i).1 (RealPinwheel.FiveSixths.checked_P9_247 i).2
          rw [← align_7 i]
          have he : 3324 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 3387
          ·
            let i : Fin 32 := ⟨j.val - 3355, by omega⟩
            apply of_witness A (witnessP9_248 i) 1800 (RealPinwheel.FiveSixths.checked_P9_248 i).1 (RealPinwheel.FiveSixths.checked_P9_248 i).2
            rw [← align_8 i]
            have he : 3355 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 32 := ⟨j.val - 3387, by omega⟩
            apply of_witness A (witnessP9_249 i) 1800 (RealPinwheel.FiveSixths.checked_P9_249 i).1 (RealPinwheel.FiveSixths.checked_P9_249 i).2
            rw [← align_9 i]
            have he : 3387 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 3585
    ·
      by_cases h10_15 : j.val < 3485
      ·
        by_cases h10_12 : j.val < 3452
        ·
          let i : Fin 33 := ⟨j.val - 3419, by omega⟩
          apply of_witness A (witnessP9_250 i) 1800 (RealPinwheel.FiveSixths.checked_P9_250 i).1 (RealPinwheel.FiveSixths.checked_P9_250 i).2
          rw [← align_10 i]
          have he : 3419 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 33 := ⟨j.val - 3452, by omega⟩
          apply of_witness A (witnessP9_251 i) 1800 (RealPinwheel.FiveSixths.checked_P9_251 i).1 (RealPinwheel.FiveSixths.checked_P9_251 i).2
          rw [← align_11 i]
          have he : 3452 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 3518
        ·
          let i : Fin 33 := ⟨j.val - 3485, by omega⟩
          apply of_witness A (witnessP9_252 i) 1800 (RealPinwheel.FiveSixths.checked_P9_252 i).1 (RealPinwheel.FiveSixths.checked_P9_252 i).2
          rw [← align_12 i]
          have he : 3485 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 3551
          ·
            let i : Fin 33 := ⟨j.val - 3518, by omega⟩
            apply of_witness A (witnessP9_253 i) 1800 (RealPinwheel.FiveSixths.checked_P9_253 i).1 (RealPinwheel.FiveSixths.checked_P9_253 i).2
            rw [← align_13 i]
            have he : 3518 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 34 := ⟨j.val - 3551, by omega⟩
            apply of_witness A (witnessP9_254 i) 1800 (RealPinwheel.FiveSixths.checked_P9_254 i).1 (RealPinwheel.FiveSixths.checked_P9_254 i).2
            rw [← align_14 i]
            have he : 3551 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 3653
      ·
        by_cases h15_17 : j.val < 3619
        ·
          let i : Fin 34 := ⟨j.val - 3585, by omega⟩
          apply of_witness A (witnessP9_255 i) 1800 (RealPinwheel.FiveSixths.checked_P9_255 i).1 (RealPinwheel.FiveSixths.checked_P9_255 i).2
          rw [← align_15 i]
          have he : 3585 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 34 := ⟨j.val - 3619, by omega⟩
          apply of_witness A (witnessP9_256 i) 1800 (RealPinwheel.FiveSixths.checked_P9_256 i).1 (RealPinwheel.FiveSixths.checked_P9_256 i).2
          rw [← align_16 i]
          have he : 3619 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 3687
        ·
          let i : Fin 34 := ⟨j.val - 3653, by omega⟩
          apply of_witness A (witnessP9_257 i) 1800 (RealPinwheel.FiveSixths.checked_P9_257 i).1 (RealPinwheel.FiveSixths.checked_P9_257 i).2
          rw [← align_17 i]
          have he : 3653 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 3721
          ·
            let i : Fin 34 := ⟨j.val - 3687, by omega⟩
            apply of_witness A (witnessP9_258 i) 1800 (RealPinwheel.FiveSixths.checked_P9_258 i).1 (RealPinwheel.FiveSixths.checked_P9_258 i).2
            rw [← align_18 i]
            have he : 3687 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 35 := ⟨j.val - 3721, by omega⟩
            apply of_witness A (witnessP9_259 i) 1800 (RealPinwheel.FiveSixths.checked_P9_259 i).1 (RealPinwheel.FiveSixths.checked_P9_259 i).2
            rw [← align_19 i]
            have he : 3721 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
