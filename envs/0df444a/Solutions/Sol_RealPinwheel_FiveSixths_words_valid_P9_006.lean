-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_006
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:33:00.979262+00:00
-- url     : https://prove2.me/submissions/01060ef8-8e34-4e4d-8c02-c934846451c3

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_120
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_121
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_122
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_123
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_124
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_125
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_126
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_127
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_128
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_129
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_130
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_131
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_132
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_133
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_134
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_135
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_136
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_137
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_138
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_139
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
    (hlo : 746 ≤ j.val) (hhi : j.val < 1002)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 12, codeFunctionP9 (746 + i.val) = (witnessP9_120 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 12, codeFunctionP9 (758 + i.val) = (witnessP9_121 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 12, codeFunctionP9 (770 + i.val) = (witnessP9_122 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 12, codeFunctionP9 (782 + i.val) = (witnessP9_123 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 12, codeFunctionP9 (794 + i.val) = (witnessP9_124 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 12, codeFunctionP9 (806 + i.val) = (witnessP9_125 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 12, codeFunctionP9 (818 + i.val) = (witnessP9_126 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 13, codeFunctionP9 (830 + i.val) = (witnessP9_127 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 13, codeFunctionP9 (843 + i.val) = (witnessP9_128 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 13, codeFunctionP9 (856 + i.val) = (witnessP9_129 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 13, codeFunctionP9 (869 + i.val) = (witnessP9_130 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 13, codeFunctionP9 (882 + i.val) = (witnessP9_131 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 13, codeFunctionP9 (895 + i.val) = (witnessP9_132 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 13, codeFunctionP9 (908 + i.val) = (witnessP9_133 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 13, codeFunctionP9 (921 + i.val) = (witnessP9_134 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 13, codeFunctionP9 (934 + i.val) = (witnessP9_135 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 13, codeFunctionP9 (947 + i.val) = (witnessP9_136 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 14, codeFunctionP9 (960 + i.val) = (witnessP9_137 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 14, codeFunctionP9 (974 + i.val) = (witnessP9_138 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 14, codeFunctionP9 (988 + i.val) = (witnessP9_139 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 869
  ·
    by_cases h0_10 : j.val < 806
    ·
      by_cases h0_5 : j.val < 770
      ·
        by_cases h0_2 : j.val < 758
        ·
          let i : Fin 12 := ⟨j.val - 746, by omega⟩
          apply of_witness A (witnessP9_120 i) 1800 (RealPinwheel.FiveSixths.checked_P9_120 i).1 (RealPinwheel.FiveSixths.checked_P9_120 i).2
          rw [← align_0 i]
          have he : 746 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 12 := ⟨j.val - 758, by omega⟩
          apply of_witness A (witnessP9_121 i) 1800 (RealPinwheel.FiveSixths.checked_P9_121 i).1 (RealPinwheel.FiveSixths.checked_P9_121 i).2
          rw [← align_1 i]
          have he : 758 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 782
        ·
          let i : Fin 12 := ⟨j.val - 770, by omega⟩
          apply of_witness A (witnessP9_122 i) 1800 (RealPinwheel.FiveSixths.checked_P9_122 i).1 (RealPinwheel.FiveSixths.checked_P9_122 i).2
          rw [← align_2 i]
          have he : 770 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 794
          ·
            let i : Fin 12 := ⟨j.val - 782, by omega⟩
            apply of_witness A (witnessP9_123 i) 1800 (RealPinwheel.FiveSixths.checked_P9_123 i).1 (RealPinwheel.FiveSixths.checked_P9_123 i).2
            rw [← align_3 i]
            have he : 782 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 12 := ⟨j.val - 794, by omega⟩
            apply of_witness A (witnessP9_124 i) 1800 (RealPinwheel.FiveSixths.checked_P9_124 i).1 (RealPinwheel.FiveSixths.checked_P9_124 i).2
            rw [← align_4 i]
            have he : 794 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 830
      ·
        by_cases h5_7 : j.val < 818
        ·
          let i : Fin 12 := ⟨j.val - 806, by omega⟩
          apply of_witness A (witnessP9_125 i) 1800 (RealPinwheel.FiveSixths.checked_P9_125 i).1 (RealPinwheel.FiveSixths.checked_P9_125 i).2
          rw [← align_5 i]
          have he : 806 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 12 := ⟨j.val - 818, by omega⟩
          apply of_witness A (witnessP9_126 i) 1800 (RealPinwheel.FiveSixths.checked_P9_126 i).1 (RealPinwheel.FiveSixths.checked_P9_126 i).2
          rw [← align_6 i]
          have he : 818 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 843
        ·
          let i : Fin 13 := ⟨j.val - 830, by omega⟩
          apply of_witness A (witnessP9_127 i) 1800 (RealPinwheel.FiveSixths.checked_P9_127 i).1 (RealPinwheel.FiveSixths.checked_P9_127 i).2
          rw [← align_7 i]
          have he : 830 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 856
          ·
            let i : Fin 13 := ⟨j.val - 843, by omega⟩
            apply of_witness A (witnessP9_128 i) 1800 (RealPinwheel.FiveSixths.checked_P9_128 i).1 (RealPinwheel.FiveSixths.checked_P9_128 i).2
            rw [← align_8 i]
            have he : 843 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 13 := ⟨j.val - 856, by omega⟩
            apply of_witness A (witnessP9_129 i) 1800 (RealPinwheel.FiveSixths.checked_P9_129 i).1 (RealPinwheel.FiveSixths.checked_P9_129 i).2
            rw [← align_9 i]
            have he : 856 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 934
    ·
      by_cases h10_15 : j.val < 895
      ·
        by_cases h10_12 : j.val < 882
        ·
          let i : Fin 13 := ⟨j.val - 869, by omega⟩
          apply of_witness A (witnessP9_130 i) 1800 (RealPinwheel.FiveSixths.checked_P9_130 i).1 (RealPinwheel.FiveSixths.checked_P9_130 i).2
          rw [← align_10 i]
          have he : 869 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 13 := ⟨j.val - 882, by omega⟩
          apply of_witness A (witnessP9_131 i) 1800 (RealPinwheel.FiveSixths.checked_P9_131 i).1 (RealPinwheel.FiveSixths.checked_P9_131 i).2
          rw [← align_11 i]
          have he : 882 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 908
        ·
          let i : Fin 13 := ⟨j.val - 895, by omega⟩
          apply of_witness A (witnessP9_132 i) 1800 (RealPinwheel.FiveSixths.checked_P9_132 i).1 (RealPinwheel.FiveSixths.checked_P9_132 i).2
          rw [← align_12 i]
          have he : 895 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 921
          ·
            let i : Fin 13 := ⟨j.val - 908, by omega⟩
            apply of_witness A (witnessP9_133 i) 1800 (RealPinwheel.FiveSixths.checked_P9_133 i).1 (RealPinwheel.FiveSixths.checked_P9_133 i).2
            rw [← align_13 i]
            have he : 908 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 13 := ⟨j.val - 921, by omega⟩
            apply of_witness A (witnessP9_134 i) 1800 (RealPinwheel.FiveSixths.checked_P9_134 i).1 (RealPinwheel.FiveSixths.checked_P9_134 i).2
            rw [← align_14 i]
            have he : 921 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 960
      ·
        by_cases h15_17 : j.val < 947
        ·
          let i : Fin 13 := ⟨j.val - 934, by omega⟩
          apply of_witness A (witnessP9_135 i) 1800 (RealPinwheel.FiveSixths.checked_P9_135 i).1 (RealPinwheel.FiveSixths.checked_P9_135 i).2
          rw [← align_15 i]
          have he : 934 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 13 := ⟨j.val - 947, by omega⟩
          apply of_witness A (witnessP9_136 i) 1800 (RealPinwheel.FiveSixths.checked_P9_136 i).1 (RealPinwheel.FiveSixths.checked_P9_136 i).2
          rw [← align_16 i]
          have he : 947 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 974
        ·
          let i : Fin 14 := ⟨j.val - 960, by omega⟩
          apply of_witness A (witnessP9_137 i) 1800 (RealPinwheel.FiveSixths.checked_P9_137 i).1 (RealPinwheel.FiveSixths.checked_P9_137 i).2
          rw [← align_17 i]
          have he : 960 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 988
          ·
            let i : Fin 14 := ⟨j.val - 974, by omega⟩
            apply of_witness A (witnessP9_138 i) 1800 (RealPinwheel.FiveSixths.checked_P9_138 i).1 (RealPinwheel.FiveSixths.checked_P9_138 i).2
            rw [← align_18 i]
            have he : 974 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 14 := ⟨j.val - 988, by omega⟩
            apply of_witness A (witnessP9_139 i) 1800 (RealPinwheel.FiveSixths.checked_P9_139 i).1 (RealPinwheel.FiveSixths.checked_P9_139 i).2
            rw [← align_19 i]
            have he : 988 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
