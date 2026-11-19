-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_small_009
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:48:13.079191+00:00
-- url     : https://prove2.me/submissions/409d7c3b-fb88-41a5-b8e0-183bdee256af

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_180
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_181
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_182
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_183
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_184
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_185
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_186
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_187
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_188
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_189
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_190
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_191
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_192
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_193
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_194
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_195
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_196
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_197
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_198
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_199
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
    (hlo : 1816 ≤ j.val) (hhi : j.val < 2228)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 19, codeFunctionD8 (1816 + i.val) = (witnessD8_180 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 19, codeFunctionD8 (1835 + i.val) = (witnessD8_181 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 19, codeFunctionD8 (1854 + i.val) = (witnessD8_182 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 19, codeFunctionD8 (1873 + i.val) = (witnessD8_183 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 20, codeFunctionD8 (1892 + i.val) = (witnessD8_184 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 20, codeFunctionD8 (1912 + i.val) = (witnessD8_185 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 20, codeFunctionD8 (1932 + i.val) = (witnessD8_186 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 20, codeFunctionD8 (1952 + i.val) = (witnessD8_187 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 20, codeFunctionD8 (1972 + i.val) = (witnessD8_188 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 20, codeFunctionD8 (1992 + i.val) = (witnessD8_189 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 20, codeFunctionD8 (2012 + i.val) = (witnessD8_190 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 21, codeFunctionD8 (2032 + i.val) = (witnessD8_191 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 21, codeFunctionD8 (2053 + i.val) = (witnessD8_192 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 22, codeFunctionD8 (2074 + i.val) = (witnessD8_193 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 22, codeFunctionD8 (2096 + i.val) = (witnessD8_194 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 22, codeFunctionD8 (2118 + i.val) = (witnessD8_195 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 22, codeFunctionD8 (2140 + i.val) = (witnessD8_196 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 22, codeFunctionD8 (2162 + i.val) = (witnessD8_197 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 22, codeFunctionD8 (2184 + i.val) = (witnessD8_198 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 22, codeFunctionD8 (2206 + i.val) = (witnessD8_199 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 2012
  ·
    by_cases h0_10 : j.val < 1912
    ·
      by_cases h0_5 : j.val < 1854
      ·
        by_cases h0_2 : j.val < 1835
        ·
          let i : Fin 19 := ⟨j.val - 1816, by omega⟩
          apply of_witness A (witnessD8_180 i) 608 (RealPinwheel.FiveSixths.checked_D8_180 i).1 (RealPinwheel.FiveSixths.checked_D8_180 i).2
          rw [← align_0 i]
          have he : 1816 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 19 := ⟨j.val - 1835, by omega⟩
          apply of_witness A (witnessD8_181 i) 608 (RealPinwheel.FiveSixths.checked_D8_181 i).1 (RealPinwheel.FiveSixths.checked_D8_181 i).2
          rw [← align_1 i]
          have he : 1835 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 1873
        ·
          let i : Fin 19 := ⟨j.val - 1854, by omega⟩
          apply of_witness A (witnessD8_182 i) 608 (RealPinwheel.FiveSixths.checked_D8_182 i).1 (RealPinwheel.FiveSixths.checked_D8_182 i).2
          rw [← align_2 i]
          have he : 1854 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 1892
          ·
            let i : Fin 19 := ⟨j.val - 1873, by omega⟩
            apply of_witness A (witnessD8_183 i) 608 (RealPinwheel.FiveSixths.checked_D8_183 i).1 (RealPinwheel.FiveSixths.checked_D8_183 i).2
            rw [← align_3 i]
            have he : 1873 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 20 := ⟨j.val - 1892, by omega⟩
            apply of_witness A (witnessD8_184 i) 608 (RealPinwheel.FiveSixths.checked_D8_184 i).1 (RealPinwheel.FiveSixths.checked_D8_184 i).2
            rw [← align_4 i]
            have he : 1892 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 1952
      ·
        by_cases h5_7 : j.val < 1932
        ·
          let i : Fin 20 := ⟨j.val - 1912, by omega⟩
          apply of_witness A (witnessD8_185 i) 608 (RealPinwheel.FiveSixths.checked_D8_185 i).1 (RealPinwheel.FiveSixths.checked_D8_185 i).2
          rw [← align_5 i]
          have he : 1912 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 20 := ⟨j.val - 1932, by omega⟩
          apply of_witness A (witnessD8_186 i) 608 (RealPinwheel.FiveSixths.checked_D8_186 i).1 (RealPinwheel.FiveSixths.checked_D8_186 i).2
          rw [← align_6 i]
          have he : 1932 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 1972
        ·
          let i : Fin 20 := ⟨j.val - 1952, by omega⟩
          apply of_witness A (witnessD8_187 i) 608 (RealPinwheel.FiveSixths.checked_D8_187 i).1 (RealPinwheel.FiveSixths.checked_D8_187 i).2
          rw [← align_7 i]
          have he : 1952 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 1992
          ·
            let i : Fin 20 := ⟨j.val - 1972, by omega⟩
            apply of_witness A (witnessD8_188 i) 608 (RealPinwheel.FiveSixths.checked_D8_188 i).1 (RealPinwheel.FiveSixths.checked_D8_188 i).2
            rw [← align_8 i]
            have he : 1972 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 20 := ⟨j.val - 1992, by omega⟩
            apply of_witness A (witnessD8_189 i) 608 (RealPinwheel.FiveSixths.checked_D8_189 i).1 (RealPinwheel.FiveSixths.checked_D8_189 i).2
            rw [← align_9 i]
            have he : 1992 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 2118
    ·
      by_cases h10_15 : j.val < 2053
      ·
        by_cases h10_12 : j.val < 2032
        ·
          let i : Fin 20 := ⟨j.val - 2012, by omega⟩
          apply of_witness A (witnessD8_190 i) 608 (RealPinwheel.FiveSixths.checked_D8_190 i).1 (RealPinwheel.FiveSixths.checked_D8_190 i).2
          rw [← align_10 i]
          have he : 2012 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 21 := ⟨j.val - 2032, by omega⟩
          apply of_witness A (witnessD8_191 i) 608 (RealPinwheel.FiveSixths.checked_D8_191 i).1 (RealPinwheel.FiveSixths.checked_D8_191 i).2
          rw [← align_11 i]
          have he : 2032 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 2074
        ·
          let i : Fin 21 := ⟨j.val - 2053, by omega⟩
          apply of_witness A (witnessD8_192 i) 608 (RealPinwheel.FiveSixths.checked_D8_192 i).1 (RealPinwheel.FiveSixths.checked_D8_192 i).2
          rw [← align_12 i]
          have he : 2053 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 2096
          ·
            let i : Fin 22 := ⟨j.val - 2074, by omega⟩
            apply of_witness A (witnessD8_193 i) 608 (RealPinwheel.FiveSixths.checked_D8_193 i).1 (RealPinwheel.FiveSixths.checked_D8_193 i).2
            rw [← align_13 i]
            have he : 2074 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 22 := ⟨j.val - 2096, by omega⟩
            apply of_witness A (witnessD8_194 i) 608 (RealPinwheel.FiveSixths.checked_D8_194 i).1 (RealPinwheel.FiveSixths.checked_D8_194 i).2
            rw [← align_14 i]
            have he : 2096 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 2162
      ·
        by_cases h15_17 : j.val < 2140
        ·
          let i : Fin 22 := ⟨j.val - 2118, by omega⟩
          apply of_witness A (witnessD8_195 i) 608 (RealPinwheel.FiveSixths.checked_D8_195 i).1 (RealPinwheel.FiveSixths.checked_D8_195 i).2
          rw [← align_15 i]
          have he : 2118 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 22 := ⟨j.val - 2140, by omega⟩
          apply of_witness A (witnessD8_196 i) 608 (RealPinwheel.FiveSixths.checked_D8_196 i).1 (RealPinwheel.FiveSixths.checked_D8_196 i).2
          rw [← align_16 i]
          have he : 2140 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 2184
        ·
          let i : Fin 22 := ⟨j.val - 2162, by omega⟩
          apply of_witness A (witnessD8_197 i) 608 (RealPinwheel.FiveSixths.checked_D8_197 i).1 (RealPinwheel.FiveSixths.checked_D8_197 i).2
          rw [← align_17 i]
          have he : 2162 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 2206
          ·
            let i : Fin 22 := ⟨j.val - 2184, by omega⟩
            apply of_witness A (witnessD8_198 i) 608 (RealPinwheel.FiveSixths.checked_D8_198 i).1 (RealPinwheel.FiveSixths.checked_D8_198 i).2
            rw [← align_18 i]
            have he : 2184 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 22 := ⟨j.val - 2206, by omega⟩
            apply of_witness A (witnessD8_199 i) 608 (RealPinwheel.FiveSixths.checked_D8_199 i).1 (RealPinwheel.FiveSixths.checked_D8_199 i).2
            rw [← align_19 i]
            have he : 2206 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
