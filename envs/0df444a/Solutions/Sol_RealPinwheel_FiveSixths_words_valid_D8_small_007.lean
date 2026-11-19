-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_small_007
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:22:32.10206+00:00
-- url     : https://prove2.me/submissions/89bec3cd-8d2b-4bdc-91df-42c6e6e87fa5

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_140
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_141
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_142
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_143
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_144
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_145
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_146
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_147
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_148
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_149
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_150
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_151
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_152
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_153
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_154
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_155
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_156
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_157
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_158
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_159
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
    (hlo : 1157 ≤ j.val) (hhi : j.val < 1464)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 14, codeFunctionD8 (1157 + i.val) = (witnessD8_140 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 15, codeFunctionD8 (1171 + i.val) = (witnessD8_141 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 15, codeFunctionD8 (1186 + i.val) = (witnessD8_142 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 15, codeFunctionD8 (1201 + i.val) = (witnessD8_143 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 15, codeFunctionD8 (1216 + i.val) = (witnessD8_144 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 15, codeFunctionD8 (1231 + i.val) = (witnessD8_145 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 15, codeFunctionD8 (1246 + i.val) = (witnessD8_146 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 15, codeFunctionD8 (1261 + i.val) = (witnessD8_147 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 15, codeFunctionD8 (1276 + i.val) = (witnessD8_148 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 15, codeFunctionD8 (1291 + i.val) = (witnessD8_149 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 15, codeFunctionD8 (1306 + i.val) = (witnessD8_150 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 15, codeFunctionD8 (1321 + i.val) = (witnessD8_151 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 16, codeFunctionD8 (1336 + i.val) = (witnessD8_152 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 16, codeFunctionD8 (1352 + i.val) = (witnessD8_153 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 16, codeFunctionD8 (1368 + i.val) = (witnessD8_154 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 16, codeFunctionD8 (1384 + i.val) = (witnessD8_155 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 16, codeFunctionD8 (1400 + i.val) = (witnessD8_156 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 16, codeFunctionD8 (1416 + i.val) = (witnessD8_157 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 16, codeFunctionD8 (1432 + i.val) = (witnessD8_158 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 16, codeFunctionD8 (1448 + i.val) = (witnessD8_159 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 1306
  ·
    by_cases h0_10 : j.val < 1231
    ·
      by_cases h0_5 : j.val < 1186
      ·
        by_cases h0_2 : j.val < 1171
        ·
          let i : Fin 14 := ⟨j.val - 1157, by omega⟩
          apply of_witness A (witnessD8_140 i) 608 (RealPinwheel.FiveSixths.checked_D8_140 i).1 (RealPinwheel.FiveSixths.checked_D8_140 i).2
          rw [← align_0 i]
          have he : 1157 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 15 := ⟨j.val - 1171, by omega⟩
          apply of_witness A (witnessD8_141 i) 608 (RealPinwheel.FiveSixths.checked_D8_141 i).1 (RealPinwheel.FiveSixths.checked_D8_141 i).2
          rw [← align_1 i]
          have he : 1171 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 1201
        ·
          let i : Fin 15 := ⟨j.val - 1186, by omega⟩
          apply of_witness A (witnessD8_142 i) 608 (RealPinwheel.FiveSixths.checked_D8_142 i).1 (RealPinwheel.FiveSixths.checked_D8_142 i).2
          rw [← align_2 i]
          have he : 1186 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 1216
          ·
            let i : Fin 15 := ⟨j.val - 1201, by omega⟩
            apply of_witness A (witnessD8_143 i) 608 (RealPinwheel.FiveSixths.checked_D8_143 i).1 (RealPinwheel.FiveSixths.checked_D8_143 i).2
            rw [← align_3 i]
            have he : 1201 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 15 := ⟨j.val - 1216, by omega⟩
            apply of_witness A (witnessD8_144 i) 608 (RealPinwheel.FiveSixths.checked_D8_144 i).1 (RealPinwheel.FiveSixths.checked_D8_144 i).2
            rw [← align_4 i]
            have he : 1216 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 1261
      ·
        by_cases h5_7 : j.val < 1246
        ·
          let i : Fin 15 := ⟨j.val - 1231, by omega⟩
          apply of_witness A (witnessD8_145 i) 608 (RealPinwheel.FiveSixths.checked_D8_145 i).1 (RealPinwheel.FiveSixths.checked_D8_145 i).2
          rw [← align_5 i]
          have he : 1231 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 15 := ⟨j.val - 1246, by omega⟩
          apply of_witness A (witnessD8_146 i) 608 (RealPinwheel.FiveSixths.checked_D8_146 i).1 (RealPinwheel.FiveSixths.checked_D8_146 i).2
          rw [← align_6 i]
          have he : 1246 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 1276
        ·
          let i : Fin 15 := ⟨j.val - 1261, by omega⟩
          apply of_witness A (witnessD8_147 i) 608 (RealPinwheel.FiveSixths.checked_D8_147 i).1 (RealPinwheel.FiveSixths.checked_D8_147 i).2
          rw [← align_7 i]
          have he : 1261 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 1291
          ·
            let i : Fin 15 := ⟨j.val - 1276, by omega⟩
            apply of_witness A (witnessD8_148 i) 608 (RealPinwheel.FiveSixths.checked_D8_148 i).1 (RealPinwheel.FiveSixths.checked_D8_148 i).2
            rw [← align_8 i]
            have he : 1276 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 15 := ⟨j.val - 1291, by omega⟩
            apply of_witness A (witnessD8_149 i) 608 (RealPinwheel.FiveSixths.checked_D8_149 i).1 (RealPinwheel.FiveSixths.checked_D8_149 i).2
            rw [← align_9 i]
            have he : 1291 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 1384
    ·
      by_cases h10_15 : j.val < 1336
      ·
        by_cases h10_12 : j.val < 1321
        ·
          let i : Fin 15 := ⟨j.val - 1306, by omega⟩
          apply of_witness A (witnessD8_150 i) 608 (RealPinwheel.FiveSixths.checked_D8_150 i).1 (RealPinwheel.FiveSixths.checked_D8_150 i).2
          rw [← align_10 i]
          have he : 1306 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 15 := ⟨j.val - 1321, by omega⟩
          apply of_witness A (witnessD8_151 i) 608 (RealPinwheel.FiveSixths.checked_D8_151 i).1 (RealPinwheel.FiveSixths.checked_D8_151 i).2
          rw [← align_11 i]
          have he : 1321 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 1352
        ·
          let i : Fin 16 := ⟨j.val - 1336, by omega⟩
          apply of_witness A (witnessD8_152 i) 608 (RealPinwheel.FiveSixths.checked_D8_152 i).1 (RealPinwheel.FiveSixths.checked_D8_152 i).2
          rw [← align_12 i]
          have he : 1336 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 1368
          ·
            let i : Fin 16 := ⟨j.val - 1352, by omega⟩
            apply of_witness A (witnessD8_153 i) 608 (RealPinwheel.FiveSixths.checked_D8_153 i).1 (RealPinwheel.FiveSixths.checked_D8_153 i).2
            rw [← align_13 i]
            have he : 1352 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 16 := ⟨j.val - 1368, by omega⟩
            apply of_witness A (witnessD8_154 i) 608 (RealPinwheel.FiveSixths.checked_D8_154 i).1 (RealPinwheel.FiveSixths.checked_D8_154 i).2
            rw [← align_14 i]
            have he : 1368 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 1416
      ·
        by_cases h15_17 : j.val < 1400
        ·
          let i : Fin 16 := ⟨j.val - 1384, by omega⟩
          apply of_witness A (witnessD8_155 i) 608 (RealPinwheel.FiveSixths.checked_D8_155 i).1 (RealPinwheel.FiveSixths.checked_D8_155 i).2
          rw [← align_15 i]
          have he : 1384 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 16 := ⟨j.val - 1400, by omega⟩
          apply of_witness A (witnessD8_156 i) 608 (RealPinwheel.FiveSixths.checked_D8_156 i).1 (RealPinwheel.FiveSixths.checked_D8_156 i).2
          rw [← align_16 i]
          have he : 1400 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 1432
        ·
          let i : Fin 16 := ⟨j.val - 1416, by omega⟩
          apply of_witness A (witnessD8_157 i) 608 (RealPinwheel.FiveSixths.checked_D8_157 i).1 (RealPinwheel.FiveSixths.checked_D8_157 i).2
          rw [← align_17 i]
          have he : 1416 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 1448
          ·
            let i : Fin 16 := ⟨j.val - 1432, by omega⟩
            apply of_witness A (witnessD8_158 i) 608 (RealPinwheel.FiveSixths.checked_D8_158 i).1 (RealPinwheel.FiveSixths.checked_D8_158 i).2
            rw [← align_18 i]
            have he : 1432 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 16 := ⟨j.val - 1448, by omega⟩
            apply of_witness A (witnessD8_159 i) 608 (RealPinwheel.FiveSixths.checked_D8_159 i).1 (RealPinwheel.FiveSixths.checked_D8_159 i).2
            rw [← align_19 i]
            have he : 1448 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
