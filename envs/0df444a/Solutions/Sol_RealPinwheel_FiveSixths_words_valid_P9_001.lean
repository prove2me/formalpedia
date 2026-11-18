-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_001
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:11:36.382212+00:00
-- url     : https://prove2.me/submissions/25ad1bd0-7414-4b34-b3b0-4262b30fc3de

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_020
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_021
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_022
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_023
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_024
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_025
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_026
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_027
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_028
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_029
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_030
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_031
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_032
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_033
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_034
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_035
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_036
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_037
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_038
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_039
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
    (hlo : 32 ≤ j.val) (hhi : j.val < 113)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 3, codeFunctionP9 (32 + i.val) = (witnessP9_020 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 3, codeFunctionP9 (35 + i.val) = (witnessP9_021 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 3, codeFunctionP9 (38 + i.val) = (witnessP9_022 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 3, codeFunctionP9 (41 + i.val) = (witnessP9_023 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 3, codeFunctionP9 (44 + i.val) = (witnessP9_024 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 3, codeFunctionP9 (47 + i.val) = (witnessP9_025 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 4, codeFunctionP9 (50 + i.val) = (witnessP9_026 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 4, codeFunctionP9 (54 + i.val) = (witnessP9_027 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 4, codeFunctionP9 (58 + i.val) = (witnessP9_028 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 4, codeFunctionP9 (62 + i.val) = (witnessP9_029 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 4, codeFunctionP9 (66 + i.val) = (witnessP9_030 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 4, codeFunctionP9 (70 + i.val) = (witnessP9_031 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 4, codeFunctionP9 (74 + i.val) = (witnessP9_032 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 5, codeFunctionP9 (78 + i.val) = (witnessP9_033 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 5, codeFunctionP9 (83 + i.val) = (witnessP9_034 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 5, codeFunctionP9 (88 + i.val) = (witnessP9_035 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 5, codeFunctionP9 (93 + i.val) = (witnessP9_036 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 5, codeFunctionP9 (98 + i.val) = (witnessP9_037 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 5, codeFunctionP9 (103 + i.val) = (witnessP9_038 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 5, codeFunctionP9 (108 + i.val) = (witnessP9_039 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 66
  ·
    by_cases h0_10 : j.val < 47
    ·
      by_cases h0_5 : j.val < 38
      ·
        by_cases h0_2 : j.val < 35
        ·
          let i : Fin 3 := ⟨j.val - 32, by omega⟩
          apply of_witness A (witnessP9_020 i) 1800 (RealPinwheel.FiveSixths.checked_P9_020 i).1 (RealPinwheel.FiveSixths.checked_P9_020 i).2
          rw [← align_0 i]
          have he : 32 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 3 := ⟨j.val - 35, by omega⟩
          apply of_witness A (witnessP9_021 i) 1800 (RealPinwheel.FiveSixths.checked_P9_021 i).1 (RealPinwheel.FiveSixths.checked_P9_021 i).2
          rw [← align_1 i]
          have he : 35 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 41
        ·
          let i : Fin 3 := ⟨j.val - 38, by omega⟩
          apply of_witness A (witnessP9_022 i) 1800 (RealPinwheel.FiveSixths.checked_P9_022 i).1 (RealPinwheel.FiveSixths.checked_P9_022 i).2
          rw [← align_2 i]
          have he : 38 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 44
          ·
            let i : Fin 3 := ⟨j.val - 41, by omega⟩
            apply of_witness A (witnessP9_023 i) 1800 (RealPinwheel.FiveSixths.checked_P9_023 i).1 (RealPinwheel.FiveSixths.checked_P9_023 i).2
            rw [← align_3 i]
            have he : 41 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 3 := ⟨j.val - 44, by omega⟩
            apply of_witness A (witnessP9_024 i) 1800 (RealPinwheel.FiveSixths.checked_P9_024 i).1 (RealPinwheel.FiveSixths.checked_P9_024 i).2
            rw [← align_4 i]
            have he : 44 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 54
      ·
        by_cases h5_7 : j.val < 50
        ·
          let i : Fin 3 := ⟨j.val - 47, by omega⟩
          apply of_witness A (witnessP9_025 i) 1800 (RealPinwheel.FiveSixths.checked_P9_025 i).1 (RealPinwheel.FiveSixths.checked_P9_025 i).2
          rw [← align_5 i]
          have he : 47 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 4 := ⟨j.val - 50, by omega⟩
          apply of_witness A (witnessP9_026 i) 1800 (RealPinwheel.FiveSixths.checked_P9_026 i).1 (RealPinwheel.FiveSixths.checked_P9_026 i).2
          rw [← align_6 i]
          have he : 50 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 58
        ·
          let i : Fin 4 := ⟨j.val - 54, by omega⟩
          apply of_witness A (witnessP9_027 i) 1800 (RealPinwheel.FiveSixths.checked_P9_027 i).1 (RealPinwheel.FiveSixths.checked_P9_027 i).2
          rw [← align_7 i]
          have he : 54 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 62
          ·
            let i : Fin 4 := ⟨j.val - 58, by omega⟩
            apply of_witness A (witnessP9_028 i) 1800 (RealPinwheel.FiveSixths.checked_P9_028 i).1 (RealPinwheel.FiveSixths.checked_P9_028 i).2
            rw [← align_8 i]
            have he : 58 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 4 := ⟨j.val - 62, by omega⟩
            apply of_witness A (witnessP9_029 i) 1800 (RealPinwheel.FiveSixths.checked_P9_029 i).1 (RealPinwheel.FiveSixths.checked_P9_029 i).2
            rw [← align_9 i]
            have he : 62 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 88
    ·
      by_cases h10_15 : j.val < 74
      ·
        by_cases h10_12 : j.val < 70
        ·
          let i : Fin 4 := ⟨j.val - 66, by omega⟩
          apply of_witness A (witnessP9_030 i) 1800 (RealPinwheel.FiveSixths.checked_P9_030 i).1 (RealPinwheel.FiveSixths.checked_P9_030 i).2
          rw [← align_10 i]
          have he : 66 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 4 := ⟨j.val - 70, by omega⟩
          apply of_witness A (witnessP9_031 i) 1800 (RealPinwheel.FiveSixths.checked_P9_031 i).1 (RealPinwheel.FiveSixths.checked_P9_031 i).2
          rw [← align_11 i]
          have he : 70 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 78
        ·
          let i : Fin 4 := ⟨j.val - 74, by omega⟩
          apply of_witness A (witnessP9_032 i) 1800 (RealPinwheel.FiveSixths.checked_P9_032 i).1 (RealPinwheel.FiveSixths.checked_P9_032 i).2
          rw [← align_12 i]
          have he : 74 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 83
          ·
            let i : Fin 5 := ⟨j.val - 78, by omega⟩
            apply of_witness A (witnessP9_033 i) 1800 (RealPinwheel.FiveSixths.checked_P9_033 i).1 (RealPinwheel.FiveSixths.checked_P9_033 i).2
            rw [← align_13 i]
            have he : 78 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 5 := ⟨j.val - 83, by omega⟩
            apply of_witness A (witnessP9_034 i) 1800 (RealPinwheel.FiveSixths.checked_P9_034 i).1 (RealPinwheel.FiveSixths.checked_P9_034 i).2
            rw [← align_14 i]
            have he : 83 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 98
      ·
        by_cases h15_17 : j.val < 93
        ·
          let i : Fin 5 := ⟨j.val - 88, by omega⟩
          apply of_witness A (witnessP9_035 i) 1800 (RealPinwheel.FiveSixths.checked_P9_035 i).1 (RealPinwheel.FiveSixths.checked_P9_035 i).2
          rw [← align_15 i]
          have he : 88 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 5 := ⟨j.val - 93, by omega⟩
          apply of_witness A (witnessP9_036 i) 1800 (RealPinwheel.FiveSixths.checked_P9_036 i).1 (RealPinwheel.FiveSixths.checked_P9_036 i).2
          rw [← align_16 i]
          have he : 93 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 103
        ·
          let i : Fin 5 := ⟨j.val - 98, by omega⟩
          apply of_witness A (witnessP9_037 i) 1800 (RealPinwheel.FiveSixths.checked_P9_037 i).1 (RealPinwheel.FiveSixths.checked_P9_037 i).2
          rw [← align_17 i]
          have he : 98 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 108
          ·
            let i : Fin 5 := ⟨j.val - 103, by omega⟩
            apply of_witness A (witnessP9_038 i) 1800 (RealPinwheel.FiveSixths.checked_P9_038 i).1 (RealPinwheel.FiveSixths.checked_P9_038 i).2
            rw [← align_18 i]
            have he : 103 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 5 := ⟨j.val - 108, by omega⟩
            apply of_witness A (witnessP9_039 i) 1800 (RealPinwheel.FiveSixths.checked_P9_039 i).1 (RealPinwheel.FiveSixths.checked_P9_039 i).2
            rw [← align_19 i]
            have he : 108 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
