-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_011
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:33:22.61525+00:00
-- url     : https://prove2.me/submissions/f4c6c677-48ab-415f-986a-4ab453e07675

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_220
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_221
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_222
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_223
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_224
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_225
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_226
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_227
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_228
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_229
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_230
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_231
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_232
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_233
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_234
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_235
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_236
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_237
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_238
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_239
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
    (hlo : 2558 ≤ j.val) (hhi : j.val < 3108)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 26, codeFunctionP9 (2558 + i.val) = (witnessP9_220 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 26, codeFunctionP9 (2584 + i.val) = (witnessP9_221 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 26, codeFunctionP9 (2610 + i.val) = (witnessP9_222 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 26, codeFunctionP9 (2636 + i.val) = (witnessP9_223 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 27, codeFunctionP9 (2662 + i.val) = (witnessP9_224 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 27, codeFunctionP9 (2689 + i.val) = (witnessP9_225 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 27, codeFunctionP9 (2716 + i.val) = (witnessP9_226 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 27, codeFunctionP9 (2743 + i.val) = (witnessP9_227 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 27, codeFunctionP9 (2770 + i.val) = (witnessP9_228 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 27, codeFunctionP9 (2797 + i.val) = (witnessP9_229 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 28, codeFunctionP9 (2824 + i.val) = (witnessP9_230 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 28, codeFunctionP9 (2852 + i.val) = (witnessP9_231 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 28, codeFunctionP9 (2880 + i.val) = (witnessP9_232 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 28, codeFunctionP9 (2908 + i.val) = (witnessP9_233 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 28, codeFunctionP9 (2936 + i.val) = (witnessP9_234 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 28, codeFunctionP9 (2964 + i.val) = (witnessP9_235 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 29, codeFunctionP9 (2992 + i.val) = (witnessP9_236 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 29, codeFunctionP9 (3021 + i.val) = (witnessP9_237 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 29, codeFunctionP9 (3050 + i.val) = (witnessP9_238 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 29, codeFunctionP9 (3079 + i.val) = (witnessP9_239 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 2824
  ·
    by_cases h0_10 : j.val < 2689
    ·
      by_cases h0_5 : j.val < 2610
      ·
        by_cases h0_2 : j.val < 2584
        ·
          let i : Fin 26 := ⟨j.val - 2558, by omega⟩
          apply of_witness A (witnessP9_220 i) 1800 (RealPinwheel.FiveSixths.checked_P9_220 i).1 (RealPinwheel.FiveSixths.checked_P9_220 i).2
          rw [← align_0 i]
          have he : 2558 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 26 := ⟨j.val - 2584, by omega⟩
          apply of_witness A (witnessP9_221 i) 1800 (RealPinwheel.FiveSixths.checked_P9_221 i).1 (RealPinwheel.FiveSixths.checked_P9_221 i).2
          rw [← align_1 i]
          have he : 2584 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 2636
        ·
          let i : Fin 26 := ⟨j.val - 2610, by omega⟩
          apply of_witness A (witnessP9_222 i) 1800 (RealPinwheel.FiveSixths.checked_P9_222 i).1 (RealPinwheel.FiveSixths.checked_P9_222 i).2
          rw [← align_2 i]
          have he : 2610 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 2662
          ·
            let i : Fin 26 := ⟨j.val - 2636, by omega⟩
            apply of_witness A (witnessP9_223 i) 1800 (RealPinwheel.FiveSixths.checked_P9_223 i).1 (RealPinwheel.FiveSixths.checked_P9_223 i).2
            rw [← align_3 i]
            have he : 2636 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 27 := ⟨j.val - 2662, by omega⟩
            apply of_witness A (witnessP9_224 i) 1800 (RealPinwheel.FiveSixths.checked_P9_224 i).1 (RealPinwheel.FiveSixths.checked_P9_224 i).2
            rw [← align_4 i]
            have he : 2662 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 2743
      ·
        by_cases h5_7 : j.val < 2716
        ·
          let i : Fin 27 := ⟨j.val - 2689, by omega⟩
          apply of_witness A (witnessP9_225 i) 1800 (RealPinwheel.FiveSixths.checked_P9_225 i).1 (RealPinwheel.FiveSixths.checked_P9_225 i).2
          rw [← align_5 i]
          have he : 2689 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 27 := ⟨j.val - 2716, by omega⟩
          apply of_witness A (witnessP9_226 i) 1800 (RealPinwheel.FiveSixths.checked_P9_226 i).1 (RealPinwheel.FiveSixths.checked_P9_226 i).2
          rw [← align_6 i]
          have he : 2716 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 2770
        ·
          let i : Fin 27 := ⟨j.val - 2743, by omega⟩
          apply of_witness A (witnessP9_227 i) 1800 (RealPinwheel.FiveSixths.checked_P9_227 i).1 (RealPinwheel.FiveSixths.checked_P9_227 i).2
          rw [← align_7 i]
          have he : 2743 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 2797
          ·
            let i : Fin 27 := ⟨j.val - 2770, by omega⟩
            apply of_witness A (witnessP9_228 i) 1800 (RealPinwheel.FiveSixths.checked_P9_228 i).1 (RealPinwheel.FiveSixths.checked_P9_228 i).2
            rw [← align_8 i]
            have he : 2770 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 27 := ⟨j.val - 2797, by omega⟩
            apply of_witness A (witnessP9_229 i) 1800 (RealPinwheel.FiveSixths.checked_P9_229 i).1 (RealPinwheel.FiveSixths.checked_P9_229 i).2
            rw [← align_9 i]
            have he : 2797 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 2964
    ·
      by_cases h10_15 : j.val < 2880
      ·
        by_cases h10_12 : j.val < 2852
        ·
          let i : Fin 28 := ⟨j.val - 2824, by omega⟩
          apply of_witness A (witnessP9_230 i) 1800 (RealPinwheel.FiveSixths.checked_P9_230 i).1 (RealPinwheel.FiveSixths.checked_P9_230 i).2
          rw [← align_10 i]
          have he : 2824 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 28 := ⟨j.val - 2852, by omega⟩
          apply of_witness A (witnessP9_231 i) 1800 (RealPinwheel.FiveSixths.checked_P9_231 i).1 (RealPinwheel.FiveSixths.checked_P9_231 i).2
          rw [← align_11 i]
          have he : 2852 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 2908
        ·
          let i : Fin 28 := ⟨j.val - 2880, by omega⟩
          apply of_witness A (witnessP9_232 i) 1800 (RealPinwheel.FiveSixths.checked_P9_232 i).1 (RealPinwheel.FiveSixths.checked_P9_232 i).2
          rw [← align_12 i]
          have he : 2880 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 2936
          ·
            let i : Fin 28 := ⟨j.val - 2908, by omega⟩
            apply of_witness A (witnessP9_233 i) 1800 (RealPinwheel.FiveSixths.checked_P9_233 i).1 (RealPinwheel.FiveSixths.checked_P9_233 i).2
            rw [← align_13 i]
            have he : 2908 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 28 := ⟨j.val - 2936, by omega⟩
            apply of_witness A (witnessP9_234 i) 1800 (RealPinwheel.FiveSixths.checked_P9_234 i).1 (RealPinwheel.FiveSixths.checked_P9_234 i).2
            rw [← align_14 i]
            have he : 2936 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 3021
      ·
        by_cases h15_17 : j.val < 2992
        ·
          let i : Fin 28 := ⟨j.val - 2964, by omega⟩
          apply of_witness A (witnessP9_235 i) 1800 (RealPinwheel.FiveSixths.checked_P9_235 i).1 (RealPinwheel.FiveSixths.checked_P9_235 i).2
          rw [← align_15 i]
          have he : 2964 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 29 := ⟨j.val - 2992, by omega⟩
          apply of_witness A (witnessP9_236 i) 1800 (RealPinwheel.FiveSixths.checked_P9_236 i).1 (RealPinwheel.FiveSixths.checked_P9_236 i).2
          rw [← align_16 i]
          have he : 2992 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 3050
        ·
          let i : Fin 29 := ⟨j.val - 3021, by omega⟩
          apply of_witness A (witnessP9_237 i) 1800 (RealPinwheel.FiveSixths.checked_P9_237 i).1 (RealPinwheel.FiveSixths.checked_P9_237 i).2
          rw [← align_17 i]
          have he : 3021 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 3079
          ·
            let i : Fin 29 := ⟨j.val - 3050, by omega⟩
            apply of_witness A (witnessP9_238 i) 1800 (RealPinwheel.FiveSixths.checked_P9_238 i).1 (RealPinwheel.FiveSixths.checked_P9_238 i).2
            rw [← align_18 i]
            have he : 3050 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 29 := ⟨j.val - 3079, by omega⟩
            apply of_witness A (witnessP9_239 i) 1800 (RealPinwheel.FiveSixths.checked_P9_239 i).1 (RealPinwheel.FiveSixths.checked_P9_239 i).2
            rw [← align_19 i]
            have he : 3079 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
