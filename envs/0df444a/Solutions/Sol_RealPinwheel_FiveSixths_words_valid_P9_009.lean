-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_009
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:41:40.530242+00:00
-- url     : https://prove2.me/submissions/61e6d18c-44a6-47a4-bd60-90691e38fb15

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_180
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_181
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_182
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_183
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_184
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_185
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_186
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_187
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_188
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_189
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_190
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_191
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_192
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_193
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_194
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_195
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_196
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_197
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_198
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_199
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
    (hlo : 1654 ≤ j.val) (hhi : j.val < 2070)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 19, codeFunctionP9 (1654 + i.val) = (witnessP9_180 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 19, codeFunctionP9 (1673 + i.val) = (witnessP9_181 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 19, codeFunctionP9 (1692 + i.val) = (witnessP9_182 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 20, codeFunctionP9 (1711 + i.val) = (witnessP9_183 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 20, codeFunctionP9 (1731 + i.val) = (witnessP9_184 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 20, codeFunctionP9 (1751 + i.val) = (witnessP9_185 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 20, codeFunctionP9 (1771 + i.val) = (witnessP9_186 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 20, codeFunctionP9 (1791 + i.val) = (witnessP9_187 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 20, codeFunctionP9 (1811 + i.val) = (witnessP9_188 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 21, codeFunctionP9 (1831 + i.val) = (witnessP9_189 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 21, codeFunctionP9 (1852 + i.val) = (witnessP9_190 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 21, codeFunctionP9 (1873 + i.val) = (witnessP9_191 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 22, codeFunctionP9 (1894 + i.val) = (witnessP9_192 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 22, codeFunctionP9 (1916 + i.val) = (witnessP9_193 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 22, codeFunctionP9 (1938 + i.val) = (witnessP9_194 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 22, codeFunctionP9 (1960 + i.val) = (witnessP9_195 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 22, codeFunctionP9 (1982 + i.val) = (witnessP9_196 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 22, codeFunctionP9 (2004 + i.val) = (witnessP9_197 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 22, codeFunctionP9 (2026 + i.val) = (witnessP9_198 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 22, codeFunctionP9 (2048 + i.val) = (witnessP9_199 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 1852
  ·
    by_cases h0_10 : j.val < 1751
    ·
      by_cases h0_5 : j.val < 1692
      ·
        by_cases h0_2 : j.val < 1673
        ·
          let i : Fin 19 := ⟨j.val - 1654, by omega⟩
          apply of_witness A (witnessP9_180 i) 1800 (RealPinwheel.FiveSixths.checked_P9_180 i).1 (RealPinwheel.FiveSixths.checked_P9_180 i).2
          rw [← align_0 i]
          have he : 1654 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 19 := ⟨j.val - 1673, by omega⟩
          apply of_witness A (witnessP9_181 i) 1800 (RealPinwheel.FiveSixths.checked_P9_181 i).1 (RealPinwheel.FiveSixths.checked_P9_181 i).2
          rw [← align_1 i]
          have he : 1673 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 1711
        ·
          let i : Fin 19 := ⟨j.val - 1692, by omega⟩
          apply of_witness A (witnessP9_182 i) 1800 (RealPinwheel.FiveSixths.checked_P9_182 i).1 (RealPinwheel.FiveSixths.checked_P9_182 i).2
          rw [← align_2 i]
          have he : 1692 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 1731
          ·
            let i : Fin 20 := ⟨j.val - 1711, by omega⟩
            apply of_witness A (witnessP9_183 i) 1800 (RealPinwheel.FiveSixths.checked_P9_183 i).1 (RealPinwheel.FiveSixths.checked_P9_183 i).2
            rw [← align_3 i]
            have he : 1711 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 20 := ⟨j.val - 1731, by omega⟩
            apply of_witness A (witnessP9_184 i) 1800 (RealPinwheel.FiveSixths.checked_P9_184 i).1 (RealPinwheel.FiveSixths.checked_P9_184 i).2
            rw [← align_4 i]
            have he : 1731 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 1791
      ·
        by_cases h5_7 : j.val < 1771
        ·
          let i : Fin 20 := ⟨j.val - 1751, by omega⟩
          apply of_witness A (witnessP9_185 i) 1800 (RealPinwheel.FiveSixths.checked_P9_185 i).1 (RealPinwheel.FiveSixths.checked_P9_185 i).2
          rw [← align_5 i]
          have he : 1751 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 20 := ⟨j.val - 1771, by omega⟩
          apply of_witness A (witnessP9_186 i) 1800 (RealPinwheel.FiveSixths.checked_P9_186 i).1 (RealPinwheel.FiveSixths.checked_P9_186 i).2
          rw [← align_6 i]
          have he : 1771 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 1811
        ·
          let i : Fin 20 := ⟨j.val - 1791, by omega⟩
          apply of_witness A (witnessP9_187 i) 1800 (RealPinwheel.FiveSixths.checked_P9_187 i).1 (RealPinwheel.FiveSixths.checked_P9_187 i).2
          rw [← align_7 i]
          have he : 1791 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 1831
          ·
            let i : Fin 20 := ⟨j.val - 1811, by omega⟩
            apply of_witness A (witnessP9_188 i) 1800 (RealPinwheel.FiveSixths.checked_P9_188 i).1 (RealPinwheel.FiveSixths.checked_P9_188 i).2
            rw [← align_8 i]
            have he : 1811 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 21 := ⟨j.val - 1831, by omega⟩
            apply of_witness A (witnessP9_189 i) 1800 (RealPinwheel.FiveSixths.checked_P9_189 i).1 (RealPinwheel.FiveSixths.checked_P9_189 i).2
            rw [← align_9 i]
            have he : 1831 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 1960
    ·
      by_cases h10_15 : j.val < 1894
      ·
        by_cases h10_12 : j.val < 1873
        ·
          let i : Fin 21 := ⟨j.val - 1852, by omega⟩
          apply of_witness A (witnessP9_190 i) 1800 (RealPinwheel.FiveSixths.checked_P9_190 i).1 (RealPinwheel.FiveSixths.checked_P9_190 i).2
          rw [← align_10 i]
          have he : 1852 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 21 := ⟨j.val - 1873, by omega⟩
          apply of_witness A (witnessP9_191 i) 1800 (RealPinwheel.FiveSixths.checked_P9_191 i).1 (RealPinwheel.FiveSixths.checked_P9_191 i).2
          rw [← align_11 i]
          have he : 1873 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 1916
        ·
          let i : Fin 22 := ⟨j.val - 1894, by omega⟩
          apply of_witness A (witnessP9_192 i) 1800 (RealPinwheel.FiveSixths.checked_P9_192 i).1 (RealPinwheel.FiveSixths.checked_P9_192 i).2
          rw [← align_12 i]
          have he : 1894 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 1938
          ·
            let i : Fin 22 := ⟨j.val - 1916, by omega⟩
            apply of_witness A (witnessP9_193 i) 1800 (RealPinwheel.FiveSixths.checked_P9_193 i).1 (RealPinwheel.FiveSixths.checked_P9_193 i).2
            rw [← align_13 i]
            have he : 1916 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 22 := ⟨j.val - 1938, by omega⟩
            apply of_witness A (witnessP9_194 i) 1800 (RealPinwheel.FiveSixths.checked_P9_194 i).1 (RealPinwheel.FiveSixths.checked_P9_194 i).2
            rw [← align_14 i]
            have he : 1938 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 2004
      ·
        by_cases h15_17 : j.val < 1982
        ·
          let i : Fin 22 := ⟨j.val - 1960, by omega⟩
          apply of_witness A (witnessP9_195 i) 1800 (RealPinwheel.FiveSixths.checked_P9_195 i).1 (RealPinwheel.FiveSixths.checked_P9_195 i).2
          rw [← align_15 i]
          have he : 1960 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 22 := ⟨j.val - 1982, by omega⟩
          apply of_witness A (witnessP9_196 i) 1800 (RealPinwheel.FiveSixths.checked_P9_196 i).1 (RealPinwheel.FiveSixths.checked_P9_196 i).2
          rw [← align_16 i]
          have he : 1982 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 2026
        ·
          let i : Fin 22 := ⟨j.val - 2004, by omega⟩
          apply of_witness A (witnessP9_197 i) 1800 (RealPinwheel.FiveSixths.checked_P9_197 i).1 (RealPinwheel.FiveSixths.checked_P9_197 i).2
          rw [← align_17 i]
          have he : 2004 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 2048
          ·
            let i : Fin 22 := ⟨j.val - 2026, by omega⟩
            apply of_witness A (witnessP9_198 i) 1800 (RealPinwheel.FiveSixths.checked_P9_198 i).1 (RealPinwheel.FiveSixths.checked_P9_198 i).2
            rw [← align_18 i]
            have he : 2026 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 22 := ⟨j.val - 2048, by omega⟩
            apply of_witness A (witnessP9_199 i) 1800 (RealPinwheel.FiveSixths.checked_P9_199 i).1 (RealPinwheel.FiveSixths.checked_P9_199 i).2
            rw [← align_19 i]
            have he : 2048 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
