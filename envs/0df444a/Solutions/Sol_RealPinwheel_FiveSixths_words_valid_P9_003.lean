-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_003
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:06:14.400507+00:00
-- url     : https://prove2.me/submissions/ce6eb8f7-3ad2-475d-b6a9-895421896eaf

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_060
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_061
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_062
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_063
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_064
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_065
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_066
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_067
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_068
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_069
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_070
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_071
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_072
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_073
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_074
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_075
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_076
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_077
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_078
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_079
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
    (hlo : 223 ≤ j.val) (hhi : j.val < 362)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 6, codeFunctionP9 (223 + i.val) = (witnessP9_060 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 6, codeFunctionP9 (229 + i.val) = (witnessP9_061 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 6, codeFunctionP9 (235 + i.val) = (witnessP9_062 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 6, codeFunctionP9 (241 + i.val) = (witnessP9_063 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 6, codeFunctionP9 (247 + i.val) = (witnessP9_064 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 7, codeFunctionP9 (253 + i.val) = (witnessP9_065 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 7, codeFunctionP9 (260 + i.val) = (witnessP9_066 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 7, codeFunctionP9 (267 + i.val) = (witnessP9_067 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 7, codeFunctionP9 (274 + i.val) = (witnessP9_068 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 7, codeFunctionP9 (281 + i.val) = (witnessP9_069 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 7, codeFunctionP9 (288 + i.val) = (witnessP9_070 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 7, codeFunctionP9 (295 + i.val) = (witnessP9_071 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 7, codeFunctionP9 (302 + i.val) = (witnessP9_072 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 7, codeFunctionP9 (309 + i.val) = (witnessP9_073 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 7, codeFunctionP9 (316 + i.val) = (witnessP9_074 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 7, codeFunctionP9 (323 + i.val) = (witnessP9_075 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 8, codeFunctionP9 (330 + i.val) = (witnessP9_076 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 8, codeFunctionP9 (338 + i.val) = (witnessP9_077 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 8, codeFunctionP9 (346 + i.val) = (witnessP9_078 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 8, codeFunctionP9 (354 + i.val) = (witnessP9_079 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 288
  ·
    by_cases h0_10 : j.val < 253
    ·
      by_cases h0_5 : j.val < 235
      ·
        by_cases h0_2 : j.val < 229
        ·
          let i : Fin 6 := ⟨j.val - 223, by omega⟩
          apply of_witness A (witnessP9_060 i) 1800 (RealPinwheel.FiveSixths.checked_P9_060 i).1 (RealPinwheel.FiveSixths.checked_P9_060 i).2
          rw [← align_0 i]
          have he : 223 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 6 := ⟨j.val - 229, by omega⟩
          apply of_witness A (witnessP9_061 i) 1800 (RealPinwheel.FiveSixths.checked_P9_061 i).1 (RealPinwheel.FiveSixths.checked_P9_061 i).2
          rw [← align_1 i]
          have he : 229 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 241
        ·
          let i : Fin 6 := ⟨j.val - 235, by omega⟩
          apply of_witness A (witnessP9_062 i) 1800 (RealPinwheel.FiveSixths.checked_P9_062 i).1 (RealPinwheel.FiveSixths.checked_P9_062 i).2
          rw [← align_2 i]
          have he : 235 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 247
          ·
            let i : Fin 6 := ⟨j.val - 241, by omega⟩
            apply of_witness A (witnessP9_063 i) 1800 (RealPinwheel.FiveSixths.checked_P9_063 i).1 (RealPinwheel.FiveSixths.checked_P9_063 i).2
            rw [← align_3 i]
            have he : 241 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 6 := ⟨j.val - 247, by omega⟩
            apply of_witness A (witnessP9_064 i) 1800 (RealPinwheel.FiveSixths.checked_P9_064 i).1 (RealPinwheel.FiveSixths.checked_P9_064 i).2
            rw [← align_4 i]
            have he : 247 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 267
      ·
        by_cases h5_7 : j.val < 260
        ·
          let i : Fin 7 := ⟨j.val - 253, by omega⟩
          apply of_witness A (witnessP9_065 i) 1800 (RealPinwheel.FiveSixths.checked_P9_065 i).1 (RealPinwheel.FiveSixths.checked_P9_065 i).2
          rw [← align_5 i]
          have he : 253 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 7 := ⟨j.val - 260, by omega⟩
          apply of_witness A (witnessP9_066 i) 1800 (RealPinwheel.FiveSixths.checked_P9_066 i).1 (RealPinwheel.FiveSixths.checked_P9_066 i).2
          rw [← align_6 i]
          have he : 260 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 274
        ·
          let i : Fin 7 := ⟨j.val - 267, by omega⟩
          apply of_witness A (witnessP9_067 i) 1800 (RealPinwheel.FiveSixths.checked_P9_067 i).1 (RealPinwheel.FiveSixths.checked_P9_067 i).2
          rw [← align_7 i]
          have he : 267 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 281
          ·
            let i : Fin 7 := ⟨j.val - 274, by omega⟩
            apply of_witness A (witnessP9_068 i) 1800 (RealPinwheel.FiveSixths.checked_P9_068 i).1 (RealPinwheel.FiveSixths.checked_P9_068 i).2
            rw [← align_8 i]
            have he : 274 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 7 := ⟨j.val - 281, by omega⟩
            apply of_witness A (witnessP9_069 i) 1800 (RealPinwheel.FiveSixths.checked_P9_069 i).1 (RealPinwheel.FiveSixths.checked_P9_069 i).2
            rw [← align_9 i]
            have he : 281 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 323
    ·
      by_cases h10_15 : j.val < 302
      ·
        by_cases h10_12 : j.val < 295
        ·
          let i : Fin 7 := ⟨j.val - 288, by omega⟩
          apply of_witness A (witnessP9_070 i) 1800 (RealPinwheel.FiveSixths.checked_P9_070 i).1 (RealPinwheel.FiveSixths.checked_P9_070 i).2
          rw [← align_10 i]
          have he : 288 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 7 := ⟨j.val - 295, by omega⟩
          apply of_witness A (witnessP9_071 i) 1800 (RealPinwheel.FiveSixths.checked_P9_071 i).1 (RealPinwheel.FiveSixths.checked_P9_071 i).2
          rw [← align_11 i]
          have he : 295 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 309
        ·
          let i : Fin 7 := ⟨j.val - 302, by omega⟩
          apply of_witness A (witnessP9_072 i) 1800 (RealPinwheel.FiveSixths.checked_P9_072 i).1 (RealPinwheel.FiveSixths.checked_P9_072 i).2
          rw [← align_12 i]
          have he : 302 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 316
          ·
            let i : Fin 7 := ⟨j.val - 309, by omega⟩
            apply of_witness A (witnessP9_073 i) 1800 (RealPinwheel.FiveSixths.checked_P9_073 i).1 (RealPinwheel.FiveSixths.checked_P9_073 i).2
            rw [← align_13 i]
            have he : 309 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 7 := ⟨j.val - 316, by omega⟩
            apply of_witness A (witnessP9_074 i) 1800 (RealPinwheel.FiveSixths.checked_P9_074 i).1 (RealPinwheel.FiveSixths.checked_P9_074 i).2
            rw [← align_14 i]
            have he : 316 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 338
      ·
        by_cases h15_17 : j.val < 330
        ·
          let i : Fin 7 := ⟨j.val - 323, by omega⟩
          apply of_witness A (witnessP9_075 i) 1800 (RealPinwheel.FiveSixths.checked_P9_075 i).1 (RealPinwheel.FiveSixths.checked_P9_075 i).2
          rw [← align_15 i]
          have he : 323 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 8 := ⟨j.val - 330, by omega⟩
          apply of_witness A (witnessP9_076 i) 1800 (RealPinwheel.FiveSixths.checked_P9_076 i).1 (RealPinwheel.FiveSixths.checked_P9_076 i).2
          rw [← align_16 i]
          have he : 330 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 346
        ·
          let i : Fin 8 := ⟨j.val - 338, by omega⟩
          apply of_witness A (witnessP9_077 i) 1800 (RealPinwheel.FiveSixths.checked_P9_077 i).1 (RealPinwheel.FiveSixths.checked_P9_077 i).2
          rw [← align_17 i]
          have he : 338 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 354
          ·
            let i : Fin 8 := ⟨j.val - 346, by omega⟩
            apply of_witness A (witnessP9_078 i) 1800 (RealPinwheel.FiveSixths.checked_P9_078 i).1 (RealPinwheel.FiveSixths.checked_P9_078 i).2
            rw [← align_18 i]
            have he : 346 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 8 := ⟨j.val - 354, by omega⟩
            apply of_witness A (witnessP9_079 i) 1800 (RealPinwheel.FiveSixths.checked_P9_079 i).1 (RealPinwheel.FiveSixths.checked_P9_079 i).2
            rw [← align_19 i]
            have he : 354 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
