-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_008
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:05:54.5362+00:00
-- url     : https://prove2.me/submissions/a0b61b84-f859-43d6-a21c-b29ba515531b

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_160
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_161
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_162
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_163
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_164
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_165
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_166
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_167
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_168
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_169
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_170
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_171
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_172
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_173
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_174
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_175
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_176
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_177
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_178
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_179
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
    (hlo : 1302 ≤ j.val) (hhi : j.val < 1654)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 16, codeFunctionP9 (1302 + i.val) = (witnessP9_160 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 17, codeFunctionP9 (1318 + i.val) = (witnessP9_161 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 17, codeFunctionP9 (1335 + i.val) = (witnessP9_162 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 17, codeFunctionP9 (1352 + i.val) = (witnessP9_163 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 17, codeFunctionP9 (1369 + i.val) = (witnessP9_164 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 17, codeFunctionP9 (1386 + i.val) = (witnessP9_165 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 17, codeFunctionP9 (1403 + i.val) = (witnessP9_166 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 17, codeFunctionP9 (1420 + i.val) = (witnessP9_167 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 17, codeFunctionP9 (1437 + i.val) = (witnessP9_168 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 17, codeFunctionP9 (1454 + i.val) = (witnessP9_169 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 17, codeFunctionP9 (1471 + i.val) = (witnessP9_170 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 18, codeFunctionP9 (1488 + i.val) = (witnessP9_171 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 18, codeFunctionP9 (1506 + i.val) = (witnessP9_172 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 18, codeFunctionP9 (1524 + i.val) = (witnessP9_173 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 18, codeFunctionP9 (1542 + i.val) = (witnessP9_174 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 18, codeFunctionP9 (1560 + i.val) = (witnessP9_175 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 19, codeFunctionP9 (1578 + i.val) = (witnessP9_176 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 19, codeFunctionP9 (1597 + i.val) = (witnessP9_177 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 19, codeFunctionP9 (1616 + i.val) = (witnessP9_178 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 19, codeFunctionP9 (1635 + i.val) = (witnessP9_179 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 1471
  ·
    by_cases h0_10 : j.val < 1386
    ·
      by_cases h0_5 : j.val < 1335
      ·
        by_cases h0_2 : j.val < 1318
        ·
          let i : Fin 16 := ⟨j.val - 1302, by omega⟩
          apply of_witness A (witnessP9_160 i) 1800 (RealPinwheel.FiveSixths.checked_P9_160 i).1 (RealPinwheel.FiveSixths.checked_P9_160 i).2
          rw [← align_0 i]
          have he : 1302 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 17 := ⟨j.val - 1318, by omega⟩
          apply of_witness A (witnessP9_161 i) 1800 (RealPinwheel.FiveSixths.checked_P9_161 i).1 (RealPinwheel.FiveSixths.checked_P9_161 i).2
          rw [← align_1 i]
          have he : 1318 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 1352
        ·
          let i : Fin 17 := ⟨j.val - 1335, by omega⟩
          apply of_witness A (witnessP9_162 i) 1800 (RealPinwheel.FiveSixths.checked_P9_162 i).1 (RealPinwheel.FiveSixths.checked_P9_162 i).2
          rw [← align_2 i]
          have he : 1335 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 1369
          ·
            let i : Fin 17 := ⟨j.val - 1352, by omega⟩
            apply of_witness A (witnessP9_163 i) 1800 (RealPinwheel.FiveSixths.checked_P9_163 i).1 (RealPinwheel.FiveSixths.checked_P9_163 i).2
            rw [← align_3 i]
            have he : 1352 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 17 := ⟨j.val - 1369, by omega⟩
            apply of_witness A (witnessP9_164 i) 1800 (RealPinwheel.FiveSixths.checked_P9_164 i).1 (RealPinwheel.FiveSixths.checked_P9_164 i).2
            rw [← align_4 i]
            have he : 1369 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 1420
      ·
        by_cases h5_7 : j.val < 1403
        ·
          let i : Fin 17 := ⟨j.val - 1386, by omega⟩
          apply of_witness A (witnessP9_165 i) 1800 (RealPinwheel.FiveSixths.checked_P9_165 i).1 (RealPinwheel.FiveSixths.checked_P9_165 i).2
          rw [← align_5 i]
          have he : 1386 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 17 := ⟨j.val - 1403, by omega⟩
          apply of_witness A (witnessP9_166 i) 1800 (RealPinwheel.FiveSixths.checked_P9_166 i).1 (RealPinwheel.FiveSixths.checked_P9_166 i).2
          rw [← align_6 i]
          have he : 1403 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 1437
        ·
          let i : Fin 17 := ⟨j.val - 1420, by omega⟩
          apply of_witness A (witnessP9_167 i) 1800 (RealPinwheel.FiveSixths.checked_P9_167 i).1 (RealPinwheel.FiveSixths.checked_P9_167 i).2
          rw [← align_7 i]
          have he : 1420 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 1454
          ·
            let i : Fin 17 := ⟨j.val - 1437, by omega⟩
            apply of_witness A (witnessP9_168 i) 1800 (RealPinwheel.FiveSixths.checked_P9_168 i).1 (RealPinwheel.FiveSixths.checked_P9_168 i).2
            rw [← align_8 i]
            have he : 1437 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 17 := ⟨j.val - 1454, by omega⟩
            apply of_witness A (witnessP9_169 i) 1800 (RealPinwheel.FiveSixths.checked_P9_169 i).1 (RealPinwheel.FiveSixths.checked_P9_169 i).2
            rw [← align_9 i]
            have he : 1454 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 1560
    ·
      by_cases h10_15 : j.val < 1506
      ·
        by_cases h10_12 : j.val < 1488
        ·
          let i : Fin 17 := ⟨j.val - 1471, by omega⟩
          apply of_witness A (witnessP9_170 i) 1800 (RealPinwheel.FiveSixths.checked_P9_170 i).1 (RealPinwheel.FiveSixths.checked_P9_170 i).2
          rw [← align_10 i]
          have he : 1471 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 18 := ⟨j.val - 1488, by omega⟩
          apply of_witness A (witnessP9_171 i) 1800 (RealPinwheel.FiveSixths.checked_P9_171 i).1 (RealPinwheel.FiveSixths.checked_P9_171 i).2
          rw [← align_11 i]
          have he : 1488 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 1524
        ·
          let i : Fin 18 := ⟨j.val - 1506, by omega⟩
          apply of_witness A (witnessP9_172 i) 1800 (RealPinwheel.FiveSixths.checked_P9_172 i).1 (RealPinwheel.FiveSixths.checked_P9_172 i).2
          rw [← align_12 i]
          have he : 1506 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 1542
          ·
            let i : Fin 18 := ⟨j.val - 1524, by omega⟩
            apply of_witness A (witnessP9_173 i) 1800 (RealPinwheel.FiveSixths.checked_P9_173 i).1 (RealPinwheel.FiveSixths.checked_P9_173 i).2
            rw [← align_13 i]
            have he : 1524 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 18 := ⟨j.val - 1542, by omega⟩
            apply of_witness A (witnessP9_174 i) 1800 (RealPinwheel.FiveSixths.checked_P9_174 i).1 (RealPinwheel.FiveSixths.checked_P9_174 i).2
            rw [← align_14 i]
            have he : 1542 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 1597
      ·
        by_cases h15_17 : j.val < 1578
        ·
          let i : Fin 18 := ⟨j.val - 1560, by omega⟩
          apply of_witness A (witnessP9_175 i) 1800 (RealPinwheel.FiveSixths.checked_P9_175 i).1 (RealPinwheel.FiveSixths.checked_P9_175 i).2
          rw [← align_15 i]
          have he : 1560 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 19 := ⟨j.val - 1578, by omega⟩
          apply of_witness A (witnessP9_176 i) 1800 (RealPinwheel.FiveSixths.checked_P9_176 i).1 (RealPinwheel.FiveSixths.checked_P9_176 i).2
          rw [← align_16 i]
          have he : 1578 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 1616
        ·
          let i : Fin 19 := ⟨j.val - 1597, by omega⟩
          apply of_witness A (witnessP9_177 i) 1800 (RealPinwheel.FiveSixths.checked_P9_177 i).1 (RealPinwheel.FiveSixths.checked_P9_177 i).2
          rw [← align_17 i]
          have he : 1597 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 1635
          ·
            let i : Fin 19 := ⟨j.val - 1616, by omega⟩
            apply of_witness A (witnessP9_178 i) 1800 (RealPinwheel.FiveSixths.checked_P9_178 i).1 (RealPinwheel.FiveSixths.checked_P9_178 i).2
            rw [← align_18 i]
            have he : 1616 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 19 := ⟨j.val - 1635, by omega⟩
            apply of_witness A (witnessP9_179 i) 1800 (RealPinwheel.FiveSixths.checked_P9_179 i).1 (RealPinwheel.FiveSixths.checked_P9_179 i).2
            rw [← align_19 i]
            have he : 1635 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
