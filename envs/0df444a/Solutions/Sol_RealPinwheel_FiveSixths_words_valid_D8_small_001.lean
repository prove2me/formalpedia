-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_small_001
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:08:53.626859+00:00
-- url     : https://prove2.me/submissions/cabe8024-d6ee-44f1-8bdb-cc74e11f7fd5

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_020
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_021
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_022
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_023
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_024
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_025
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_026
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_027
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_028
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_029
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_030
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_031
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_032
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_033
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_034
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_035
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_036
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_037
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_038
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_039
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
    (hlo : 51 ≤ j.val) (hhi : j.val < 152)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 4, codeFunctionD8 (51 + i.val) = (witnessD8_020 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 4, codeFunctionD8 (55 + i.val) = (witnessD8_021 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 4, codeFunctionD8 (59 + i.val) = (witnessD8_022 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 4, codeFunctionD8 (63 + i.val) = (witnessD8_023 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 5, codeFunctionD8 (67 + i.val) = (witnessD8_024 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 5, codeFunctionD8 (72 + i.val) = (witnessD8_025 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 5, codeFunctionD8 (77 + i.val) = (witnessD8_026 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 5, codeFunctionD8 (82 + i.val) = (witnessD8_027 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 5, codeFunctionD8 (87 + i.val) = (witnessD8_028 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 5, codeFunctionD8 (92 + i.val) = (witnessD8_029 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 5, codeFunctionD8 (97 + i.val) = (witnessD8_030 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 5, codeFunctionD8 (102 + i.val) = (witnessD8_031 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 5, codeFunctionD8 (107 + i.val) = (witnessD8_032 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 5, codeFunctionD8 (112 + i.val) = (witnessD8_033 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 5, codeFunctionD8 (117 + i.val) = (witnessD8_034 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 6, codeFunctionD8 (122 + i.val) = (witnessD8_035 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 6, codeFunctionD8 (128 + i.val) = (witnessD8_036 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 6, codeFunctionD8 (134 + i.val) = (witnessD8_037 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 6, codeFunctionD8 (140 + i.val) = (witnessD8_038 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 6, codeFunctionD8 (146 + i.val) = (witnessD8_039 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 97
  ·
    by_cases h0_10 : j.val < 72
    ·
      by_cases h0_5 : j.val < 59
      ·
        by_cases h0_2 : j.val < 55
        ·
          let i : Fin 4 := ⟨j.val - 51, by omega⟩
          apply of_witness A (witnessD8_020 i) 608 (RealPinwheel.FiveSixths.checked_D8_020 i).1 (RealPinwheel.FiveSixths.checked_D8_020 i).2
          rw [← align_0 i]
          have he : 51 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 4 := ⟨j.val - 55, by omega⟩
          apply of_witness A (witnessD8_021 i) 608 (RealPinwheel.FiveSixths.checked_D8_021 i).1 (RealPinwheel.FiveSixths.checked_D8_021 i).2
          rw [← align_1 i]
          have he : 55 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 63
        ·
          let i : Fin 4 := ⟨j.val - 59, by omega⟩
          apply of_witness A (witnessD8_022 i) 608 (RealPinwheel.FiveSixths.checked_D8_022 i).1 (RealPinwheel.FiveSixths.checked_D8_022 i).2
          rw [← align_2 i]
          have he : 59 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 67
          ·
            let i : Fin 4 := ⟨j.val - 63, by omega⟩
            apply of_witness A (witnessD8_023 i) 608 (RealPinwheel.FiveSixths.checked_D8_023 i).1 (RealPinwheel.FiveSixths.checked_D8_023 i).2
            rw [← align_3 i]
            have he : 63 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 5 := ⟨j.val - 67, by omega⟩
            apply of_witness A (witnessD8_024 i) 608 (RealPinwheel.FiveSixths.checked_D8_024 i).1 (RealPinwheel.FiveSixths.checked_D8_024 i).2
            rw [← align_4 i]
            have he : 67 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 82
      ·
        by_cases h5_7 : j.val < 77
        ·
          let i : Fin 5 := ⟨j.val - 72, by omega⟩
          apply of_witness A (witnessD8_025 i) 608 (RealPinwheel.FiveSixths.checked_D8_025 i).1 (RealPinwheel.FiveSixths.checked_D8_025 i).2
          rw [← align_5 i]
          have he : 72 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 5 := ⟨j.val - 77, by omega⟩
          apply of_witness A (witnessD8_026 i) 608 (RealPinwheel.FiveSixths.checked_D8_026 i).1 (RealPinwheel.FiveSixths.checked_D8_026 i).2
          rw [← align_6 i]
          have he : 77 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 87
        ·
          let i : Fin 5 := ⟨j.val - 82, by omega⟩
          apply of_witness A (witnessD8_027 i) 608 (RealPinwheel.FiveSixths.checked_D8_027 i).1 (RealPinwheel.FiveSixths.checked_D8_027 i).2
          rw [← align_7 i]
          have he : 82 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 92
          ·
            let i : Fin 5 := ⟨j.val - 87, by omega⟩
            apply of_witness A (witnessD8_028 i) 608 (RealPinwheel.FiveSixths.checked_D8_028 i).1 (RealPinwheel.FiveSixths.checked_D8_028 i).2
            rw [← align_8 i]
            have he : 87 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 5 := ⟨j.val - 92, by omega⟩
            apply of_witness A (witnessD8_029 i) 608 (RealPinwheel.FiveSixths.checked_D8_029 i).1 (RealPinwheel.FiveSixths.checked_D8_029 i).2
            rw [← align_9 i]
            have he : 92 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 122
    ·
      by_cases h10_15 : j.val < 107
      ·
        by_cases h10_12 : j.val < 102
        ·
          let i : Fin 5 := ⟨j.val - 97, by omega⟩
          apply of_witness A (witnessD8_030 i) 608 (RealPinwheel.FiveSixths.checked_D8_030 i).1 (RealPinwheel.FiveSixths.checked_D8_030 i).2
          rw [← align_10 i]
          have he : 97 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 5 := ⟨j.val - 102, by omega⟩
          apply of_witness A (witnessD8_031 i) 608 (RealPinwheel.FiveSixths.checked_D8_031 i).1 (RealPinwheel.FiveSixths.checked_D8_031 i).2
          rw [← align_11 i]
          have he : 102 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 112
        ·
          let i : Fin 5 := ⟨j.val - 107, by omega⟩
          apply of_witness A (witnessD8_032 i) 608 (RealPinwheel.FiveSixths.checked_D8_032 i).1 (RealPinwheel.FiveSixths.checked_D8_032 i).2
          rw [← align_12 i]
          have he : 107 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 117
          ·
            let i : Fin 5 := ⟨j.val - 112, by omega⟩
            apply of_witness A (witnessD8_033 i) 608 (RealPinwheel.FiveSixths.checked_D8_033 i).1 (RealPinwheel.FiveSixths.checked_D8_033 i).2
            rw [← align_13 i]
            have he : 112 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 5 := ⟨j.val - 117, by omega⟩
            apply of_witness A (witnessD8_034 i) 608 (RealPinwheel.FiveSixths.checked_D8_034 i).1 (RealPinwheel.FiveSixths.checked_D8_034 i).2
            rw [← align_14 i]
            have he : 117 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 134
      ·
        by_cases h15_17 : j.val < 128
        ·
          let i : Fin 6 := ⟨j.val - 122, by omega⟩
          apply of_witness A (witnessD8_035 i) 608 (RealPinwheel.FiveSixths.checked_D8_035 i).1 (RealPinwheel.FiveSixths.checked_D8_035 i).2
          rw [← align_15 i]
          have he : 122 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 6 := ⟨j.val - 128, by omega⟩
          apply of_witness A (witnessD8_036 i) 608 (RealPinwheel.FiveSixths.checked_D8_036 i).1 (RealPinwheel.FiveSixths.checked_D8_036 i).2
          rw [← align_16 i]
          have he : 128 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 140
        ·
          let i : Fin 6 := ⟨j.val - 134, by omega⟩
          apply of_witness A (witnessD8_037 i) 608 (RealPinwheel.FiveSixths.checked_D8_037 i).1 (RealPinwheel.FiveSixths.checked_D8_037 i).2
          rw [← align_17 i]
          have he : 134 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 146
          ·
            let i : Fin 6 := ⟨j.val - 140, by omega⟩
            apply of_witness A (witnessD8_038 i) 608 (RealPinwheel.FiveSixths.checked_D8_038 i).1 (RealPinwheel.FiveSixths.checked_D8_038 i).2
            rw [← align_18 i]
            have he : 140 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 6 := ⟨j.val - 146, by omega⟩
            apply of_witness A (witnessD8_039 i) 608 (RealPinwheel.FiveSixths.checked_D8_039 i).1 (RealPinwheel.FiveSixths.checked_D8_039 i).2
            rw [← align_19 i]
            have he : 146 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
