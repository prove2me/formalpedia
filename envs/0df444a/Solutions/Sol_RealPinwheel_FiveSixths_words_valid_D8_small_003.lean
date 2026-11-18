-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_small_003
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:40:13.048022+00:00
-- url     : https://prove2.me/submissions/d2a46144-643c-4577-b3ec-119a0018cec3

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_060
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_061
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_062
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_063
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_064
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_065
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_066
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_067
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_068
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_069
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_070
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_071
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_072
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_073
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_074
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_075
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_076
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_077
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_078
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_079
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
    (hlo : 287 ≤ j.val) (hhi : j.val < 458)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 8, codeFunctionD8 (287 + i.val) = (witnessD8_060 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 8, codeFunctionD8 (295 + i.val) = (witnessD8_061 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 8, codeFunctionD8 (303 + i.val) = (witnessD8_062 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 8, codeFunctionD8 (311 + i.val) = (witnessD8_063 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 8, codeFunctionD8 (319 + i.val) = (witnessD8_064 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 8, codeFunctionD8 (327 + i.val) = (witnessD8_065 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 8, codeFunctionD8 (335 + i.val) = (witnessD8_066 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 8, codeFunctionD8 (343 + i.val) = (witnessD8_067 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 8, codeFunctionD8 (351 + i.val) = (witnessD8_068 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 9, codeFunctionD8 (359 + i.val) = (witnessD8_069 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 9, codeFunctionD8 (368 + i.val) = (witnessD8_070 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 9, codeFunctionD8 (377 + i.val) = (witnessD8_071 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 9, codeFunctionD8 (386 + i.val) = (witnessD8_072 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 9, codeFunctionD8 (395 + i.val) = (witnessD8_073 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 9, codeFunctionD8 (404 + i.val) = (witnessD8_074 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 9, codeFunctionD8 (413 + i.val) = (witnessD8_075 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 9, codeFunctionD8 (422 + i.val) = (witnessD8_076 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 9, codeFunctionD8 (431 + i.val) = (witnessD8_077 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 9, codeFunctionD8 (440 + i.val) = (witnessD8_078 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 9, codeFunctionD8 (449 + i.val) = (witnessD8_079 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 368
  ·
    by_cases h0_10 : j.val < 327
    ·
      by_cases h0_5 : j.val < 303
      ·
        by_cases h0_2 : j.val < 295
        ·
          let i : Fin 8 := ⟨j.val - 287, by omega⟩
          apply of_witness A (witnessD8_060 i) 608 (RealPinwheel.FiveSixths.checked_D8_060 i).1 (RealPinwheel.FiveSixths.checked_D8_060 i).2
          rw [← align_0 i]
          have he : 287 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 8 := ⟨j.val - 295, by omega⟩
          apply of_witness A (witnessD8_061 i) 608 (RealPinwheel.FiveSixths.checked_D8_061 i).1 (RealPinwheel.FiveSixths.checked_D8_061 i).2
          rw [← align_1 i]
          have he : 295 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 311
        ·
          let i : Fin 8 := ⟨j.val - 303, by omega⟩
          apply of_witness A (witnessD8_062 i) 608 (RealPinwheel.FiveSixths.checked_D8_062 i).1 (RealPinwheel.FiveSixths.checked_D8_062 i).2
          rw [← align_2 i]
          have he : 303 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 319
          ·
            let i : Fin 8 := ⟨j.val - 311, by omega⟩
            apply of_witness A (witnessD8_063 i) 608 (RealPinwheel.FiveSixths.checked_D8_063 i).1 (RealPinwheel.FiveSixths.checked_D8_063 i).2
            rw [← align_3 i]
            have he : 311 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 8 := ⟨j.val - 319, by omega⟩
            apply of_witness A (witnessD8_064 i) 608 (RealPinwheel.FiveSixths.checked_D8_064 i).1 (RealPinwheel.FiveSixths.checked_D8_064 i).2
            rw [← align_4 i]
            have he : 319 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 343
      ·
        by_cases h5_7 : j.val < 335
        ·
          let i : Fin 8 := ⟨j.val - 327, by omega⟩
          apply of_witness A (witnessD8_065 i) 608 (RealPinwheel.FiveSixths.checked_D8_065 i).1 (RealPinwheel.FiveSixths.checked_D8_065 i).2
          rw [← align_5 i]
          have he : 327 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 8 := ⟨j.val - 335, by omega⟩
          apply of_witness A (witnessD8_066 i) 608 (RealPinwheel.FiveSixths.checked_D8_066 i).1 (RealPinwheel.FiveSixths.checked_D8_066 i).2
          rw [← align_6 i]
          have he : 335 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 351
        ·
          let i : Fin 8 := ⟨j.val - 343, by omega⟩
          apply of_witness A (witnessD8_067 i) 608 (RealPinwheel.FiveSixths.checked_D8_067 i).1 (RealPinwheel.FiveSixths.checked_D8_067 i).2
          rw [← align_7 i]
          have he : 343 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 359
          ·
            let i : Fin 8 := ⟨j.val - 351, by omega⟩
            apply of_witness A (witnessD8_068 i) 608 (RealPinwheel.FiveSixths.checked_D8_068 i).1 (RealPinwheel.FiveSixths.checked_D8_068 i).2
            rw [← align_8 i]
            have he : 351 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 9 := ⟨j.val - 359, by omega⟩
            apply of_witness A (witnessD8_069 i) 608 (RealPinwheel.FiveSixths.checked_D8_069 i).1 (RealPinwheel.FiveSixths.checked_D8_069 i).2
            rw [← align_9 i]
            have he : 359 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 413
    ·
      by_cases h10_15 : j.val < 386
      ·
        by_cases h10_12 : j.val < 377
        ·
          let i : Fin 9 := ⟨j.val - 368, by omega⟩
          apply of_witness A (witnessD8_070 i) 608 (RealPinwheel.FiveSixths.checked_D8_070 i).1 (RealPinwheel.FiveSixths.checked_D8_070 i).2
          rw [← align_10 i]
          have he : 368 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 9 := ⟨j.val - 377, by omega⟩
          apply of_witness A (witnessD8_071 i) 608 (RealPinwheel.FiveSixths.checked_D8_071 i).1 (RealPinwheel.FiveSixths.checked_D8_071 i).2
          rw [← align_11 i]
          have he : 377 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 395
        ·
          let i : Fin 9 := ⟨j.val - 386, by omega⟩
          apply of_witness A (witnessD8_072 i) 608 (RealPinwheel.FiveSixths.checked_D8_072 i).1 (RealPinwheel.FiveSixths.checked_D8_072 i).2
          rw [← align_12 i]
          have he : 386 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 404
          ·
            let i : Fin 9 := ⟨j.val - 395, by omega⟩
            apply of_witness A (witnessD8_073 i) 608 (RealPinwheel.FiveSixths.checked_D8_073 i).1 (RealPinwheel.FiveSixths.checked_D8_073 i).2
            rw [← align_13 i]
            have he : 395 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 9 := ⟨j.val - 404, by omega⟩
            apply of_witness A (witnessD8_074 i) 608 (RealPinwheel.FiveSixths.checked_D8_074 i).1 (RealPinwheel.FiveSixths.checked_D8_074 i).2
            rw [← align_14 i]
            have he : 404 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 431
      ·
        by_cases h15_17 : j.val < 422
        ·
          let i : Fin 9 := ⟨j.val - 413, by omega⟩
          apply of_witness A (witnessD8_075 i) 608 (RealPinwheel.FiveSixths.checked_D8_075 i).1 (RealPinwheel.FiveSixths.checked_D8_075 i).2
          rw [← align_15 i]
          have he : 413 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 9 := ⟨j.val - 422, by omega⟩
          apply of_witness A (witnessD8_076 i) 608 (RealPinwheel.FiveSixths.checked_D8_076 i).1 (RealPinwheel.FiveSixths.checked_D8_076 i).2
          rw [← align_16 i]
          have he : 422 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 440
        ·
          let i : Fin 9 := ⟨j.val - 431, by omega⟩
          apply of_witness A (witnessD8_077 i) 608 (RealPinwheel.FiveSixths.checked_D8_077 i).1 (RealPinwheel.FiveSixths.checked_D8_077 i).2
          rw [← align_17 i]
          have he : 431 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 449
          ·
            let i : Fin 9 := ⟨j.val - 440, by omega⟩
            apply of_witness A (witnessD8_078 i) 608 (RealPinwheel.FiveSixths.checked_D8_078 i).1 (RealPinwheel.FiveSixths.checked_D8_078 i).2
            rw [← align_18 i]
            have he : 440 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 9 := ⟨j.val - 449, by omega⟩
            apply of_witness A (witnessD8_079 i) 608 (RealPinwheel.FiveSixths.checked_D8_079 i).1 (RealPinwheel.FiveSixths.checked_D8_079 i).2
            rw [← align_19 i]
            have he : 449 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
