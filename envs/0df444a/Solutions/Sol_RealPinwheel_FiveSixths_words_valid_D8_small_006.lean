-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_small_006
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:03:25.335043+00:00
-- url     : https://prove2.me/submissions/32aa703d-f245-42d9-a5d9-383ab97b09ee

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_120
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_121
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_122
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_123
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_124
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_125
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_126
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_127
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_128
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_129
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_130
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_131
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_132
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_133
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_134
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_135
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_136
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_137
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_138
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_139
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
    (hlo : 890 ≤ j.val) (hhi : j.val < 1157)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 13, codeFunctionD8 (890 + i.val) = (witnessD8_120 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 13, codeFunctionD8 (903 + i.val) = (witnessD8_121 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 13, codeFunctionD8 (916 + i.val) = (witnessD8_122 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 13, codeFunctionD8 (929 + i.val) = (witnessD8_123 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 13, codeFunctionD8 (942 + i.val) = (witnessD8_124 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 13, codeFunctionD8 (955 + i.val) = (witnessD8_125 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 13, codeFunctionD8 (968 + i.val) = (witnessD8_126 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 13, codeFunctionD8 (981 + i.val) = (witnessD8_127 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 13, codeFunctionD8 (994 + i.val) = (witnessD8_128 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 13, codeFunctionD8 (1007 + i.val) = (witnessD8_129 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 13, codeFunctionD8 (1020 + i.val) = (witnessD8_130 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 13, codeFunctionD8 (1033 + i.val) = (witnessD8_131 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 13, codeFunctionD8 (1046 + i.val) = (witnessD8_132 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 14, codeFunctionD8 (1059 + i.val) = (witnessD8_133 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 14, codeFunctionD8 (1073 + i.val) = (witnessD8_134 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 14, codeFunctionD8 (1087 + i.val) = (witnessD8_135 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 14, codeFunctionD8 (1101 + i.val) = (witnessD8_136 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 14, codeFunctionD8 (1115 + i.val) = (witnessD8_137 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 14, codeFunctionD8 (1129 + i.val) = (witnessD8_138 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 14, codeFunctionD8 (1143 + i.val) = (witnessD8_139 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 1020
  ·
    by_cases h0_10 : j.val < 955
    ·
      by_cases h0_5 : j.val < 916
      ·
        by_cases h0_2 : j.val < 903
        ·
          let i : Fin 13 := ⟨j.val - 890, by omega⟩
          apply of_witness A (witnessD8_120 i) 608 (RealPinwheel.FiveSixths.checked_D8_120 i).1 (RealPinwheel.FiveSixths.checked_D8_120 i).2
          rw [← align_0 i]
          have he : 890 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 13 := ⟨j.val - 903, by omega⟩
          apply of_witness A (witnessD8_121 i) 608 (RealPinwheel.FiveSixths.checked_D8_121 i).1 (RealPinwheel.FiveSixths.checked_D8_121 i).2
          rw [← align_1 i]
          have he : 903 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 929
        ·
          let i : Fin 13 := ⟨j.val - 916, by omega⟩
          apply of_witness A (witnessD8_122 i) 608 (RealPinwheel.FiveSixths.checked_D8_122 i).1 (RealPinwheel.FiveSixths.checked_D8_122 i).2
          rw [← align_2 i]
          have he : 916 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 942
          ·
            let i : Fin 13 := ⟨j.val - 929, by omega⟩
            apply of_witness A (witnessD8_123 i) 608 (RealPinwheel.FiveSixths.checked_D8_123 i).1 (RealPinwheel.FiveSixths.checked_D8_123 i).2
            rw [← align_3 i]
            have he : 929 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 13 := ⟨j.val - 942, by omega⟩
            apply of_witness A (witnessD8_124 i) 608 (RealPinwheel.FiveSixths.checked_D8_124 i).1 (RealPinwheel.FiveSixths.checked_D8_124 i).2
            rw [← align_4 i]
            have he : 942 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 981
      ·
        by_cases h5_7 : j.val < 968
        ·
          let i : Fin 13 := ⟨j.val - 955, by omega⟩
          apply of_witness A (witnessD8_125 i) 608 (RealPinwheel.FiveSixths.checked_D8_125 i).1 (RealPinwheel.FiveSixths.checked_D8_125 i).2
          rw [← align_5 i]
          have he : 955 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 13 := ⟨j.val - 968, by omega⟩
          apply of_witness A (witnessD8_126 i) 608 (RealPinwheel.FiveSixths.checked_D8_126 i).1 (RealPinwheel.FiveSixths.checked_D8_126 i).2
          rw [← align_6 i]
          have he : 968 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 994
        ·
          let i : Fin 13 := ⟨j.val - 981, by omega⟩
          apply of_witness A (witnessD8_127 i) 608 (RealPinwheel.FiveSixths.checked_D8_127 i).1 (RealPinwheel.FiveSixths.checked_D8_127 i).2
          rw [← align_7 i]
          have he : 981 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 1007
          ·
            let i : Fin 13 := ⟨j.val - 994, by omega⟩
            apply of_witness A (witnessD8_128 i) 608 (RealPinwheel.FiveSixths.checked_D8_128 i).1 (RealPinwheel.FiveSixths.checked_D8_128 i).2
            rw [← align_8 i]
            have he : 994 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 13 := ⟨j.val - 1007, by omega⟩
            apply of_witness A (witnessD8_129 i) 608 (RealPinwheel.FiveSixths.checked_D8_129 i).1 (RealPinwheel.FiveSixths.checked_D8_129 i).2
            rw [← align_9 i]
            have he : 1007 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 1087
    ·
      by_cases h10_15 : j.val < 1046
      ·
        by_cases h10_12 : j.val < 1033
        ·
          let i : Fin 13 := ⟨j.val - 1020, by omega⟩
          apply of_witness A (witnessD8_130 i) 608 (RealPinwheel.FiveSixths.checked_D8_130 i).1 (RealPinwheel.FiveSixths.checked_D8_130 i).2
          rw [← align_10 i]
          have he : 1020 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 13 := ⟨j.val - 1033, by omega⟩
          apply of_witness A (witnessD8_131 i) 608 (RealPinwheel.FiveSixths.checked_D8_131 i).1 (RealPinwheel.FiveSixths.checked_D8_131 i).2
          rw [← align_11 i]
          have he : 1033 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 1059
        ·
          let i : Fin 13 := ⟨j.val - 1046, by omega⟩
          apply of_witness A (witnessD8_132 i) 608 (RealPinwheel.FiveSixths.checked_D8_132 i).1 (RealPinwheel.FiveSixths.checked_D8_132 i).2
          rw [← align_12 i]
          have he : 1046 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 1073
          ·
            let i : Fin 14 := ⟨j.val - 1059, by omega⟩
            apply of_witness A (witnessD8_133 i) 608 (RealPinwheel.FiveSixths.checked_D8_133 i).1 (RealPinwheel.FiveSixths.checked_D8_133 i).2
            rw [← align_13 i]
            have he : 1059 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 14 := ⟨j.val - 1073, by omega⟩
            apply of_witness A (witnessD8_134 i) 608 (RealPinwheel.FiveSixths.checked_D8_134 i).1 (RealPinwheel.FiveSixths.checked_D8_134 i).2
            rw [← align_14 i]
            have he : 1073 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 1115
      ·
        by_cases h15_17 : j.val < 1101
        ·
          let i : Fin 14 := ⟨j.val - 1087, by omega⟩
          apply of_witness A (witnessD8_135 i) 608 (RealPinwheel.FiveSixths.checked_D8_135 i).1 (RealPinwheel.FiveSixths.checked_D8_135 i).2
          rw [← align_15 i]
          have he : 1087 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 14 := ⟨j.val - 1101, by omega⟩
          apply of_witness A (witnessD8_136 i) 608 (RealPinwheel.FiveSixths.checked_D8_136 i).1 (RealPinwheel.FiveSixths.checked_D8_136 i).2
          rw [← align_16 i]
          have he : 1101 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 1129
        ·
          let i : Fin 14 := ⟨j.val - 1115, by omega⟩
          apply of_witness A (witnessD8_137 i) 608 (RealPinwheel.FiveSixths.checked_D8_137 i).1 (RealPinwheel.FiveSixths.checked_D8_137 i).2
          rw [← align_17 i]
          have he : 1115 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 1143
          ·
            let i : Fin 14 := ⟨j.val - 1129, by omega⟩
            apply of_witness A (witnessD8_138 i) 608 (RealPinwheel.FiveSixths.checked_D8_138 i).1 (RealPinwheel.FiveSixths.checked_D8_138 i).2
            rw [← align_18 i]
            have he : 1129 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 14 := ⟨j.val - 1143, by omega⟩
            apply of_witness A (witnessD8_139 i) 608 (RealPinwheel.FiveSixths.checked_D8_139 i).1 (RealPinwheel.FiveSixths.checked_D8_139 i).2
            rw [← align_19 i]
            have he : 1143 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
