-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_small_011
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:29:13.591187+00:00
-- url     : https://prove2.me/submissions/5f859398-7ae9-470f-b503-54da7d06c9b8

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_220
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_221
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_222
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_223
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_224
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_225
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_226
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_227
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_228
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_229
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_230
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_231
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_232
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_233
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_234
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_235
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_236
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_237
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_238
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_239
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
    (hlo : 2724 ≤ j.val) (hhi : j.val < 3331)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 27, codeFunctionD8 (2724 + i.val) = (witnessD8_220 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 27, codeFunctionD8 (2751 + i.val) = (witnessD8_221 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 27, codeFunctionD8 (2778 + i.val) = (witnessD8_222 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 27, codeFunctionD8 (2805 + i.val) = (witnessD8_223 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 28, codeFunctionD8 (2832 + i.val) = (witnessD8_224 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 29, codeFunctionD8 (2860 + i.val) = (witnessD8_225 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 29, codeFunctionD8 (2889 + i.val) = (witnessD8_226 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 29, codeFunctionD8 (2918 + i.val) = (witnessD8_227 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 29, codeFunctionD8 (2947 + i.val) = (witnessD8_228 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 29, codeFunctionD8 (2976 + i.val) = (witnessD8_229 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 30, codeFunctionD8 (3005 + i.val) = (witnessD8_230 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 31, codeFunctionD8 (3035 + i.val) = (witnessD8_231 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 31, codeFunctionD8 (3066 + i.val) = (witnessD8_232 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 31, codeFunctionD8 (3097 + i.val) = (witnessD8_233 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 33, codeFunctionD8 (3128 + i.val) = (witnessD8_234 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 33, codeFunctionD8 (3161 + i.val) = (witnessD8_235 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 33, codeFunctionD8 (3194 + i.val) = (witnessD8_236 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 34, codeFunctionD8 (3227 + i.val) = (witnessD8_237 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 35, codeFunctionD8 (3261 + i.val) = (witnessD8_238 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 35, codeFunctionD8 (3296 + i.val) = (witnessD8_239 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 3005
  ·
    by_cases h0_10 : j.val < 2860
    ·
      by_cases h0_5 : j.val < 2778
      ·
        by_cases h0_2 : j.val < 2751
        ·
          let i : Fin 27 := ⟨j.val - 2724, by omega⟩
          apply of_witness A (witnessD8_220 i) 608 (RealPinwheel.FiveSixths.checked_D8_220 i).1 (RealPinwheel.FiveSixths.checked_D8_220 i).2
          rw [← align_0 i]
          have he : 2724 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 27 := ⟨j.val - 2751, by omega⟩
          apply of_witness A (witnessD8_221 i) 608 (RealPinwheel.FiveSixths.checked_D8_221 i).1 (RealPinwheel.FiveSixths.checked_D8_221 i).2
          rw [← align_1 i]
          have he : 2751 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 2805
        ·
          let i : Fin 27 := ⟨j.val - 2778, by omega⟩
          apply of_witness A (witnessD8_222 i) 608 (RealPinwheel.FiveSixths.checked_D8_222 i).1 (RealPinwheel.FiveSixths.checked_D8_222 i).2
          rw [← align_2 i]
          have he : 2778 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 2832
          ·
            let i : Fin 27 := ⟨j.val - 2805, by omega⟩
            apply of_witness A (witnessD8_223 i) 608 (RealPinwheel.FiveSixths.checked_D8_223 i).1 (RealPinwheel.FiveSixths.checked_D8_223 i).2
            rw [← align_3 i]
            have he : 2805 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 28 := ⟨j.val - 2832, by omega⟩
            apply of_witness A (witnessD8_224 i) 608 (RealPinwheel.FiveSixths.checked_D8_224 i).1 (RealPinwheel.FiveSixths.checked_D8_224 i).2
            rw [← align_4 i]
            have he : 2832 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 2918
      ·
        by_cases h5_7 : j.val < 2889
        ·
          let i : Fin 29 := ⟨j.val - 2860, by omega⟩
          apply of_witness A (witnessD8_225 i) 608 (RealPinwheel.FiveSixths.checked_D8_225 i).1 (RealPinwheel.FiveSixths.checked_D8_225 i).2
          rw [← align_5 i]
          have he : 2860 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 29 := ⟨j.val - 2889, by omega⟩
          apply of_witness A (witnessD8_226 i) 608 (RealPinwheel.FiveSixths.checked_D8_226 i).1 (RealPinwheel.FiveSixths.checked_D8_226 i).2
          rw [← align_6 i]
          have he : 2889 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 2947
        ·
          let i : Fin 29 := ⟨j.val - 2918, by omega⟩
          apply of_witness A (witnessD8_227 i) 608 (RealPinwheel.FiveSixths.checked_D8_227 i).1 (RealPinwheel.FiveSixths.checked_D8_227 i).2
          rw [← align_7 i]
          have he : 2918 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 2976
          ·
            let i : Fin 29 := ⟨j.val - 2947, by omega⟩
            apply of_witness A (witnessD8_228 i) 608 (RealPinwheel.FiveSixths.checked_D8_228 i).1 (RealPinwheel.FiveSixths.checked_D8_228 i).2
            rw [← align_8 i]
            have he : 2947 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 29 := ⟨j.val - 2976, by omega⟩
            apply of_witness A (witnessD8_229 i) 608 (RealPinwheel.FiveSixths.checked_D8_229 i).1 (RealPinwheel.FiveSixths.checked_D8_229 i).2
            rw [← align_9 i]
            have he : 2976 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 3161
    ·
      by_cases h10_15 : j.val < 3066
      ·
        by_cases h10_12 : j.val < 3035
        ·
          let i : Fin 30 := ⟨j.val - 3005, by omega⟩
          apply of_witness A (witnessD8_230 i) 608 (RealPinwheel.FiveSixths.checked_D8_230 i).1 (RealPinwheel.FiveSixths.checked_D8_230 i).2
          rw [← align_10 i]
          have he : 3005 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 31 := ⟨j.val - 3035, by omega⟩
          apply of_witness A (witnessD8_231 i) 608 (RealPinwheel.FiveSixths.checked_D8_231 i).1 (RealPinwheel.FiveSixths.checked_D8_231 i).2
          rw [← align_11 i]
          have he : 3035 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 3097
        ·
          let i : Fin 31 := ⟨j.val - 3066, by omega⟩
          apply of_witness A (witnessD8_232 i) 608 (RealPinwheel.FiveSixths.checked_D8_232 i).1 (RealPinwheel.FiveSixths.checked_D8_232 i).2
          rw [← align_12 i]
          have he : 3066 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 3128
          ·
            let i : Fin 31 := ⟨j.val - 3097, by omega⟩
            apply of_witness A (witnessD8_233 i) 608 (RealPinwheel.FiveSixths.checked_D8_233 i).1 (RealPinwheel.FiveSixths.checked_D8_233 i).2
            rw [← align_13 i]
            have he : 3097 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 33 := ⟨j.val - 3128, by omega⟩
            apply of_witness A (witnessD8_234 i) 608 (RealPinwheel.FiveSixths.checked_D8_234 i).1 (RealPinwheel.FiveSixths.checked_D8_234 i).2
            rw [← align_14 i]
            have he : 3128 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 3227
      ·
        by_cases h15_17 : j.val < 3194
        ·
          let i : Fin 33 := ⟨j.val - 3161, by omega⟩
          apply of_witness A (witnessD8_235 i) 608 (RealPinwheel.FiveSixths.checked_D8_235 i).1 (RealPinwheel.FiveSixths.checked_D8_235 i).2
          rw [← align_15 i]
          have he : 3161 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 33 := ⟨j.val - 3194, by omega⟩
          apply of_witness A (witnessD8_236 i) 608 (RealPinwheel.FiveSixths.checked_D8_236 i).1 (RealPinwheel.FiveSixths.checked_D8_236 i).2
          rw [← align_16 i]
          have he : 3194 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 3261
        ·
          let i : Fin 34 := ⟨j.val - 3227, by omega⟩
          apply of_witness A (witnessD8_237 i) 608 (RealPinwheel.FiveSixths.checked_D8_237 i).1 (RealPinwheel.FiveSixths.checked_D8_237 i).2
          rw [← align_17 i]
          have he : 3227 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 3296
          ·
            let i : Fin 35 := ⟨j.val - 3261, by omega⟩
            apply of_witness A (witnessD8_238 i) 608 (RealPinwheel.FiveSixths.checked_D8_238 i).1 (RealPinwheel.FiveSixths.checked_D8_238 i).2
            rw [← align_18 i]
            have he : 3261 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 35 := ⟨j.val - 3296, by omega⟩
            apply of_witness A (witnessD8_239 i) 608 (RealPinwheel.FiveSixths.checked_D8_239 i).1 (RealPinwheel.FiveSixths.checked_D8_239 i).2
            rw [← align_19 i]
            have he : 3296 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
