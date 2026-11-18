-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D7_001
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:48:16.631495+00:00
-- url     : https://prove2.me/submissions/0f32733b-fad8-43c3-b895-d361aff4ca40

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD7
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_020
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_021
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_022
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_023
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_024
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_025
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_026
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_027
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_028
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_029
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_030
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_031
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_032
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_033
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_034
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_035
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_036
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_037
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_038
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_039
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

theorem solution (A : Instance 7) (j : Fin 1657)
    (hlo : 196 ≤ j.val) (hhi : j.val < 558)
    (hb : codeBox (codeFunctionD7 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 7), 0 < L ∧ L ≤ 352 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 15, codeFunctionD7 (196 + i.val) = (witnessD7_020 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 15, codeFunctionD7 (211 + i.val) = (witnessD7_021 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 15, codeFunctionD7 (226 + i.val) = (witnessD7_022 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 16, codeFunctionD7 (241 + i.val) = (witnessD7_023 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 16, codeFunctionD7 (257 + i.val) = (witnessD7_024 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 16, codeFunctionD7 (273 + i.val) = (witnessD7_025 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 17, codeFunctionD7 (289 + i.val) = (witnessD7_026 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 17, codeFunctionD7 (306 + i.val) = (witnessD7_027 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 17, codeFunctionD7 (323 + i.val) = (witnessD7_028 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 18, codeFunctionD7 (340 + i.val) = (witnessD7_029 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 18, codeFunctionD7 (358 + i.val) = (witnessD7_030 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 19, codeFunctionD7 (376 + i.val) = (witnessD7_031 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 19, codeFunctionD7 (395 + i.val) = (witnessD7_032 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 19, codeFunctionD7 (414 + i.val) = (witnessD7_033 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 20, codeFunctionD7 (433 + i.val) = (witnessD7_034 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 20, codeFunctionD7 (453 + i.val) = (witnessD7_035 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 20, codeFunctionD7 (473 + i.val) = (witnessD7_036 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 21, codeFunctionD7 (493 + i.val) = (witnessD7_037 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 22, codeFunctionD7 (514 + i.val) = (witnessD7_038 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 22, codeFunctionD7 (536 + i.val) = (witnessD7_039 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 358
  ·
    by_cases h0_10 : j.val < 273
    ·
      by_cases h0_5 : j.val < 226
      ·
        by_cases h0_2 : j.val < 211
        ·
          let i : Fin 15 := ⟨j.val - 196, by omega⟩
          apply of_witness A (witnessD7_020 i) 352 (RealPinwheel.FiveSixths.checked_D7_020 i).1 (RealPinwheel.FiveSixths.checked_D7_020 i).2
          rw [← align_0 i]
          have he : 196 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 15 := ⟨j.val - 211, by omega⟩
          apply of_witness A (witnessD7_021 i) 352 (RealPinwheel.FiveSixths.checked_D7_021 i).1 (RealPinwheel.FiveSixths.checked_D7_021 i).2
          rw [← align_1 i]
          have he : 211 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 241
        ·
          let i : Fin 15 := ⟨j.val - 226, by omega⟩
          apply of_witness A (witnessD7_022 i) 352 (RealPinwheel.FiveSixths.checked_D7_022 i).1 (RealPinwheel.FiveSixths.checked_D7_022 i).2
          rw [← align_2 i]
          have he : 226 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 257
          ·
            let i : Fin 16 := ⟨j.val - 241, by omega⟩
            apply of_witness A (witnessD7_023 i) 352 (RealPinwheel.FiveSixths.checked_D7_023 i).1 (RealPinwheel.FiveSixths.checked_D7_023 i).2
            rw [← align_3 i]
            have he : 241 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 16 := ⟨j.val - 257, by omega⟩
            apply of_witness A (witnessD7_024 i) 352 (RealPinwheel.FiveSixths.checked_D7_024 i).1 (RealPinwheel.FiveSixths.checked_D7_024 i).2
            rw [← align_4 i]
            have he : 257 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 306
      ·
        by_cases h5_7 : j.val < 289
        ·
          let i : Fin 16 := ⟨j.val - 273, by omega⟩
          apply of_witness A (witnessD7_025 i) 352 (RealPinwheel.FiveSixths.checked_D7_025 i).1 (RealPinwheel.FiveSixths.checked_D7_025 i).2
          rw [← align_5 i]
          have he : 273 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 17 := ⟨j.val - 289, by omega⟩
          apply of_witness A (witnessD7_026 i) 352 (RealPinwheel.FiveSixths.checked_D7_026 i).1 (RealPinwheel.FiveSixths.checked_D7_026 i).2
          rw [← align_6 i]
          have he : 289 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 323
        ·
          let i : Fin 17 := ⟨j.val - 306, by omega⟩
          apply of_witness A (witnessD7_027 i) 352 (RealPinwheel.FiveSixths.checked_D7_027 i).1 (RealPinwheel.FiveSixths.checked_D7_027 i).2
          rw [← align_7 i]
          have he : 306 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 340
          ·
            let i : Fin 17 := ⟨j.val - 323, by omega⟩
            apply of_witness A (witnessD7_028 i) 352 (RealPinwheel.FiveSixths.checked_D7_028 i).1 (RealPinwheel.FiveSixths.checked_D7_028 i).2
            rw [← align_8 i]
            have he : 323 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 18 := ⟨j.val - 340, by omega⟩
            apply of_witness A (witnessD7_029 i) 352 (RealPinwheel.FiveSixths.checked_D7_029 i).1 (RealPinwheel.FiveSixths.checked_D7_029 i).2
            rw [← align_9 i]
            have he : 340 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 453
    ·
      by_cases h10_15 : j.val < 395
      ·
        by_cases h10_12 : j.val < 376
        ·
          let i : Fin 18 := ⟨j.val - 358, by omega⟩
          apply of_witness A (witnessD7_030 i) 352 (RealPinwheel.FiveSixths.checked_D7_030 i).1 (RealPinwheel.FiveSixths.checked_D7_030 i).2
          rw [← align_10 i]
          have he : 358 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 19 := ⟨j.val - 376, by omega⟩
          apply of_witness A (witnessD7_031 i) 352 (RealPinwheel.FiveSixths.checked_D7_031 i).1 (RealPinwheel.FiveSixths.checked_D7_031 i).2
          rw [← align_11 i]
          have he : 376 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 414
        ·
          let i : Fin 19 := ⟨j.val - 395, by omega⟩
          apply of_witness A (witnessD7_032 i) 352 (RealPinwheel.FiveSixths.checked_D7_032 i).1 (RealPinwheel.FiveSixths.checked_D7_032 i).2
          rw [← align_12 i]
          have he : 395 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 433
          ·
            let i : Fin 19 := ⟨j.val - 414, by omega⟩
            apply of_witness A (witnessD7_033 i) 352 (RealPinwheel.FiveSixths.checked_D7_033 i).1 (RealPinwheel.FiveSixths.checked_D7_033 i).2
            rw [← align_13 i]
            have he : 414 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 20 := ⟨j.val - 433, by omega⟩
            apply of_witness A (witnessD7_034 i) 352 (RealPinwheel.FiveSixths.checked_D7_034 i).1 (RealPinwheel.FiveSixths.checked_D7_034 i).2
            rw [← align_14 i]
            have he : 433 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 493
      ·
        by_cases h15_17 : j.val < 473
        ·
          let i : Fin 20 := ⟨j.val - 453, by omega⟩
          apply of_witness A (witnessD7_035 i) 352 (RealPinwheel.FiveSixths.checked_D7_035 i).1 (RealPinwheel.FiveSixths.checked_D7_035 i).2
          rw [← align_15 i]
          have he : 453 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 20 := ⟨j.val - 473, by omega⟩
          apply of_witness A (witnessD7_036 i) 352 (RealPinwheel.FiveSixths.checked_D7_036 i).1 (RealPinwheel.FiveSixths.checked_D7_036 i).2
          rw [← align_16 i]
          have he : 473 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 514
        ·
          let i : Fin 21 := ⟨j.val - 493, by omega⟩
          apply of_witness A (witnessD7_037 i) 352 (RealPinwheel.FiveSixths.checked_D7_037 i).1 (RealPinwheel.FiveSixths.checked_D7_037 i).2
          rw [← align_17 i]
          have he : 493 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 536
          ·
            let i : Fin 22 := ⟨j.val - 514, by omega⟩
            apply of_witness A (witnessD7_038 i) 352 (RealPinwheel.FiveSixths.checked_D7_038 i).1 (RealPinwheel.FiveSixths.checked_D7_038 i).2
            rw [← align_18 i]
            have he : 514 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 22 := ⟨j.val - 536, by omega⟩
            apply of_witness A (witnessD7_039 i) 352 (RealPinwheel.FiveSixths.checked_D7_039 i).1 (RealPinwheel.FiveSixths.checked_D7_039 i).2
            rw [← align_19 i]
            have he : 536 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
