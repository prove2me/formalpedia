-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_007
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:03:19.29012+00:00
-- url     : https://prove2.me/submissions/a79d31d2-f9e9-482b-84ab-8a4b4eeed7cb

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_140
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_141
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_142
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_143
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_144
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_145
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_146
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_147
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_148
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_149
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_150
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_151
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_152
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_153
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_154
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_155
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_156
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_157
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_158
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_159
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
    (hlo : 1002 ≤ j.val) (hhi : j.val < 1302)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 14, codeFunctionP9 (1002 + i.val) = (witnessP9_140 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 14, codeFunctionP9 (1016 + i.val) = (witnessP9_141 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 14, codeFunctionP9 (1030 + i.val) = (witnessP9_142 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 14, codeFunctionP9 (1044 + i.val) = (witnessP9_143 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 14, codeFunctionP9 (1058 + i.val) = (witnessP9_144 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 15, codeFunctionP9 (1072 + i.val) = (witnessP9_145 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 15, codeFunctionP9 (1087 + i.val) = (witnessP9_146 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 15, codeFunctionP9 (1102 + i.val) = (witnessP9_147 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 15, codeFunctionP9 (1117 + i.val) = (witnessP9_148 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 15, codeFunctionP9 (1132 + i.val) = (witnessP9_149 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 15, codeFunctionP9 (1147 + i.val) = (witnessP9_150 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 15, codeFunctionP9 (1162 + i.val) = (witnessP9_151 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 15, codeFunctionP9 (1177 + i.val) = (witnessP9_152 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 15, codeFunctionP9 (1192 + i.val) = (witnessP9_153 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 15, codeFunctionP9 (1207 + i.val) = (witnessP9_154 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 16, codeFunctionP9 (1222 + i.val) = (witnessP9_155 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 16, codeFunctionP9 (1238 + i.val) = (witnessP9_156 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 16, codeFunctionP9 (1254 + i.val) = (witnessP9_157 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 16, codeFunctionP9 (1270 + i.val) = (witnessP9_158 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 16, codeFunctionP9 (1286 + i.val) = (witnessP9_159 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 1147
  ·
    by_cases h0_10 : j.val < 1072
    ·
      by_cases h0_5 : j.val < 1030
      ·
        by_cases h0_2 : j.val < 1016
        ·
          let i : Fin 14 := ⟨j.val - 1002, by omega⟩
          apply of_witness A (witnessP9_140 i) 1800 (RealPinwheel.FiveSixths.checked_P9_140 i).1 (RealPinwheel.FiveSixths.checked_P9_140 i).2
          rw [← align_0 i]
          have he : 1002 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 14 := ⟨j.val - 1016, by omega⟩
          apply of_witness A (witnessP9_141 i) 1800 (RealPinwheel.FiveSixths.checked_P9_141 i).1 (RealPinwheel.FiveSixths.checked_P9_141 i).2
          rw [← align_1 i]
          have he : 1016 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 1044
        ·
          let i : Fin 14 := ⟨j.val - 1030, by omega⟩
          apply of_witness A (witnessP9_142 i) 1800 (RealPinwheel.FiveSixths.checked_P9_142 i).1 (RealPinwheel.FiveSixths.checked_P9_142 i).2
          rw [← align_2 i]
          have he : 1030 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 1058
          ·
            let i : Fin 14 := ⟨j.val - 1044, by omega⟩
            apply of_witness A (witnessP9_143 i) 1800 (RealPinwheel.FiveSixths.checked_P9_143 i).1 (RealPinwheel.FiveSixths.checked_P9_143 i).2
            rw [← align_3 i]
            have he : 1044 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 14 := ⟨j.val - 1058, by omega⟩
            apply of_witness A (witnessP9_144 i) 1800 (RealPinwheel.FiveSixths.checked_P9_144 i).1 (RealPinwheel.FiveSixths.checked_P9_144 i).2
            rw [← align_4 i]
            have he : 1058 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 1102
      ·
        by_cases h5_7 : j.val < 1087
        ·
          let i : Fin 15 := ⟨j.val - 1072, by omega⟩
          apply of_witness A (witnessP9_145 i) 1800 (RealPinwheel.FiveSixths.checked_P9_145 i).1 (RealPinwheel.FiveSixths.checked_P9_145 i).2
          rw [← align_5 i]
          have he : 1072 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 15 := ⟨j.val - 1087, by omega⟩
          apply of_witness A (witnessP9_146 i) 1800 (RealPinwheel.FiveSixths.checked_P9_146 i).1 (RealPinwheel.FiveSixths.checked_P9_146 i).2
          rw [← align_6 i]
          have he : 1087 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 1117
        ·
          let i : Fin 15 := ⟨j.val - 1102, by omega⟩
          apply of_witness A (witnessP9_147 i) 1800 (RealPinwheel.FiveSixths.checked_P9_147 i).1 (RealPinwheel.FiveSixths.checked_P9_147 i).2
          rw [← align_7 i]
          have he : 1102 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 1132
          ·
            let i : Fin 15 := ⟨j.val - 1117, by omega⟩
            apply of_witness A (witnessP9_148 i) 1800 (RealPinwheel.FiveSixths.checked_P9_148 i).1 (RealPinwheel.FiveSixths.checked_P9_148 i).2
            rw [← align_8 i]
            have he : 1117 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 15 := ⟨j.val - 1132, by omega⟩
            apply of_witness A (witnessP9_149 i) 1800 (RealPinwheel.FiveSixths.checked_P9_149 i).1 (RealPinwheel.FiveSixths.checked_P9_149 i).2
            rw [← align_9 i]
            have he : 1132 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 1222
    ·
      by_cases h10_15 : j.val < 1177
      ·
        by_cases h10_12 : j.val < 1162
        ·
          let i : Fin 15 := ⟨j.val - 1147, by omega⟩
          apply of_witness A (witnessP9_150 i) 1800 (RealPinwheel.FiveSixths.checked_P9_150 i).1 (RealPinwheel.FiveSixths.checked_P9_150 i).2
          rw [← align_10 i]
          have he : 1147 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 15 := ⟨j.val - 1162, by omega⟩
          apply of_witness A (witnessP9_151 i) 1800 (RealPinwheel.FiveSixths.checked_P9_151 i).1 (RealPinwheel.FiveSixths.checked_P9_151 i).2
          rw [← align_11 i]
          have he : 1162 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 1192
        ·
          let i : Fin 15 := ⟨j.val - 1177, by omega⟩
          apply of_witness A (witnessP9_152 i) 1800 (RealPinwheel.FiveSixths.checked_P9_152 i).1 (RealPinwheel.FiveSixths.checked_P9_152 i).2
          rw [← align_12 i]
          have he : 1177 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 1207
          ·
            let i : Fin 15 := ⟨j.val - 1192, by omega⟩
            apply of_witness A (witnessP9_153 i) 1800 (RealPinwheel.FiveSixths.checked_P9_153 i).1 (RealPinwheel.FiveSixths.checked_P9_153 i).2
            rw [← align_13 i]
            have he : 1192 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 15 := ⟨j.val - 1207, by omega⟩
            apply of_witness A (witnessP9_154 i) 1800 (RealPinwheel.FiveSixths.checked_P9_154 i).1 (RealPinwheel.FiveSixths.checked_P9_154 i).2
            rw [← align_14 i]
            have he : 1207 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 1254
      ·
        by_cases h15_17 : j.val < 1238
        ·
          let i : Fin 16 := ⟨j.val - 1222, by omega⟩
          apply of_witness A (witnessP9_155 i) 1800 (RealPinwheel.FiveSixths.checked_P9_155 i).1 (RealPinwheel.FiveSixths.checked_P9_155 i).2
          rw [← align_15 i]
          have he : 1222 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 16 := ⟨j.val - 1238, by omega⟩
          apply of_witness A (witnessP9_156 i) 1800 (RealPinwheel.FiveSixths.checked_P9_156 i).1 (RealPinwheel.FiveSixths.checked_P9_156 i).2
          rw [← align_16 i]
          have he : 1238 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 1270
        ·
          let i : Fin 16 := ⟨j.val - 1254, by omega⟩
          apply of_witness A (witnessP9_157 i) 1800 (RealPinwheel.FiveSixths.checked_P9_157 i).1 (RealPinwheel.FiveSixths.checked_P9_157 i).2
          rw [← align_17 i]
          have he : 1254 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 1286
          ·
            let i : Fin 16 := ⟨j.val - 1270, by omega⟩
            apply of_witness A (witnessP9_158 i) 1800 (RealPinwheel.FiveSixths.checked_P9_158 i).1 (RealPinwheel.FiveSixths.checked_P9_158 i).2
            rw [← align_18 i]
            have he : 1270 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 16 := ⟨j.val - 1286, by omega⟩
            apply of_witness A (witnessP9_159 i) 1800 (RealPinwheel.FiveSixths.checked_P9_159 i).1 (RealPinwheel.FiveSixths.checked_P9_159 i).2
            rw [← align_19 i]
            have he : 1286 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
