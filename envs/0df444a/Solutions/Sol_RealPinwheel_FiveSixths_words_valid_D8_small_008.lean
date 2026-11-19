-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_small_008
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:33:24.267687+00:00
-- url     : https://prove2.me/submissions/ac54f99d-0370-468b-a627-7837d330c4be

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_160
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_161
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_162
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_163
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_164
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_165
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_166
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_167
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_168
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_169
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_170
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_171
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_172
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_173
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_174
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_175
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_176
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_177
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_178
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_179
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
    (hlo : 1464 ≤ j.val) (hhi : j.val < 1816)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 16, codeFunctionD8 (1464 + i.val) = (witnessD8_160 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 17, codeFunctionD8 (1480 + i.val) = (witnessD8_161 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 17, codeFunctionD8 (1497 + i.val) = (witnessD8_162 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 17, codeFunctionD8 (1514 + i.val) = (witnessD8_163 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 17, codeFunctionD8 (1531 + i.val) = (witnessD8_164 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 17, codeFunctionD8 (1548 + i.val) = (witnessD8_165 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 17, codeFunctionD8 (1565 + i.val) = (witnessD8_166 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 17, codeFunctionD8 (1582 + i.val) = (witnessD8_167 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 17, codeFunctionD8 (1599 + i.val) = (witnessD8_168 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 17, codeFunctionD8 (1616 + i.val) = (witnessD8_169 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 17, codeFunctionD8 (1633 + i.val) = (witnessD8_170 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 18, codeFunctionD8 (1650 + i.val) = (witnessD8_171 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 18, codeFunctionD8 (1668 + i.val) = (witnessD8_172 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 18, codeFunctionD8 (1686 + i.val) = (witnessD8_173 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 18, codeFunctionD8 (1704 + i.val) = (witnessD8_174 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 18, codeFunctionD8 (1722 + i.val) = (witnessD8_175 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 19, codeFunctionD8 (1740 + i.val) = (witnessD8_176 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 19, codeFunctionD8 (1759 + i.val) = (witnessD8_177 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 19, codeFunctionD8 (1778 + i.val) = (witnessD8_178 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 19, codeFunctionD8 (1797 + i.val) = (witnessD8_179 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 1633
  ·
    by_cases h0_10 : j.val < 1548
    ·
      by_cases h0_5 : j.val < 1497
      ·
        by_cases h0_2 : j.val < 1480
        ·
          let i : Fin 16 := ⟨j.val - 1464, by omega⟩
          apply of_witness A (witnessD8_160 i) 608 (RealPinwheel.FiveSixths.checked_D8_160 i).1 (RealPinwheel.FiveSixths.checked_D8_160 i).2
          rw [← align_0 i]
          have he : 1464 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 17 := ⟨j.val - 1480, by omega⟩
          apply of_witness A (witnessD8_161 i) 608 (RealPinwheel.FiveSixths.checked_D8_161 i).1 (RealPinwheel.FiveSixths.checked_D8_161 i).2
          rw [← align_1 i]
          have he : 1480 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 1514
        ·
          let i : Fin 17 := ⟨j.val - 1497, by omega⟩
          apply of_witness A (witnessD8_162 i) 608 (RealPinwheel.FiveSixths.checked_D8_162 i).1 (RealPinwheel.FiveSixths.checked_D8_162 i).2
          rw [← align_2 i]
          have he : 1497 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 1531
          ·
            let i : Fin 17 := ⟨j.val - 1514, by omega⟩
            apply of_witness A (witnessD8_163 i) 608 (RealPinwheel.FiveSixths.checked_D8_163 i).1 (RealPinwheel.FiveSixths.checked_D8_163 i).2
            rw [← align_3 i]
            have he : 1514 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 17 := ⟨j.val - 1531, by omega⟩
            apply of_witness A (witnessD8_164 i) 608 (RealPinwheel.FiveSixths.checked_D8_164 i).1 (RealPinwheel.FiveSixths.checked_D8_164 i).2
            rw [← align_4 i]
            have he : 1531 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 1582
      ·
        by_cases h5_7 : j.val < 1565
        ·
          let i : Fin 17 := ⟨j.val - 1548, by omega⟩
          apply of_witness A (witnessD8_165 i) 608 (RealPinwheel.FiveSixths.checked_D8_165 i).1 (RealPinwheel.FiveSixths.checked_D8_165 i).2
          rw [← align_5 i]
          have he : 1548 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 17 := ⟨j.val - 1565, by omega⟩
          apply of_witness A (witnessD8_166 i) 608 (RealPinwheel.FiveSixths.checked_D8_166 i).1 (RealPinwheel.FiveSixths.checked_D8_166 i).2
          rw [← align_6 i]
          have he : 1565 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 1599
        ·
          let i : Fin 17 := ⟨j.val - 1582, by omega⟩
          apply of_witness A (witnessD8_167 i) 608 (RealPinwheel.FiveSixths.checked_D8_167 i).1 (RealPinwheel.FiveSixths.checked_D8_167 i).2
          rw [← align_7 i]
          have he : 1582 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 1616
          ·
            let i : Fin 17 := ⟨j.val - 1599, by omega⟩
            apply of_witness A (witnessD8_168 i) 608 (RealPinwheel.FiveSixths.checked_D8_168 i).1 (RealPinwheel.FiveSixths.checked_D8_168 i).2
            rw [← align_8 i]
            have he : 1599 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 17 := ⟨j.val - 1616, by omega⟩
            apply of_witness A (witnessD8_169 i) 608 (RealPinwheel.FiveSixths.checked_D8_169 i).1 (RealPinwheel.FiveSixths.checked_D8_169 i).2
            rw [← align_9 i]
            have he : 1616 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 1722
    ·
      by_cases h10_15 : j.val < 1668
      ·
        by_cases h10_12 : j.val < 1650
        ·
          let i : Fin 17 := ⟨j.val - 1633, by omega⟩
          apply of_witness A (witnessD8_170 i) 608 (RealPinwheel.FiveSixths.checked_D8_170 i).1 (RealPinwheel.FiveSixths.checked_D8_170 i).2
          rw [← align_10 i]
          have he : 1633 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 18 := ⟨j.val - 1650, by omega⟩
          apply of_witness A (witnessD8_171 i) 608 (RealPinwheel.FiveSixths.checked_D8_171 i).1 (RealPinwheel.FiveSixths.checked_D8_171 i).2
          rw [← align_11 i]
          have he : 1650 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 1686
        ·
          let i : Fin 18 := ⟨j.val - 1668, by omega⟩
          apply of_witness A (witnessD8_172 i) 608 (RealPinwheel.FiveSixths.checked_D8_172 i).1 (RealPinwheel.FiveSixths.checked_D8_172 i).2
          rw [← align_12 i]
          have he : 1668 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 1704
          ·
            let i : Fin 18 := ⟨j.val - 1686, by omega⟩
            apply of_witness A (witnessD8_173 i) 608 (RealPinwheel.FiveSixths.checked_D8_173 i).1 (RealPinwheel.FiveSixths.checked_D8_173 i).2
            rw [← align_13 i]
            have he : 1686 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 18 := ⟨j.val - 1704, by omega⟩
            apply of_witness A (witnessD8_174 i) 608 (RealPinwheel.FiveSixths.checked_D8_174 i).1 (RealPinwheel.FiveSixths.checked_D8_174 i).2
            rw [← align_14 i]
            have he : 1704 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 1759
      ·
        by_cases h15_17 : j.val < 1740
        ·
          let i : Fin 18 := ⟨j.val - 1722, by omega⟩
          apply of_witness A (witnessD8_175 i) 608 (RealPinwheel.FiveSixths.checked_D8_175 i).1 (RealPinwheel.FiveSixths.checked_D8_175 i).2
          rw [← align_15 i]
          have he : 1722 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 19 := ⟨j.val - 1740, by omega⟩
          apply of_witness A (witnessD8_176 i) 608 (RealPinwheel.FiveSixths.checked_D8_176 i).1 (RealPinwheel.FiveSixths.checked_D8_176 i).2
          rw [← align_16 i]
          have he : 1740 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 1778
        ·
          let i : Fin 19 := ⟨j.val - 1759, by omega⟩
          apply of_witness A (witnessD8_177 i) 608 (RealPinwheel.FiveSixths.checked_D8_177 i).1 (RealPinwheel.FiveSixths.checked_D8_177 i).2
          rw [← align_17 i]
          have he : 1759 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 1797
          ·
            let i : Fin 19 := ⟨j.val - 1778, by omega⟩
            apply of_witness A (witnessD8_178 i) 608 (RealPinwheel.FiveSixths.checked_D8_178 i).1 (RealPinwheel.FiveSixths.checked_D8_178 i).2
            rw [← align_18 i]
            have he : 1778 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 19 := ⟨j.val - 1797, by omega⟩
            apply of_witness A (witnessD8_179 i) 608 (RealPinwheel.FiveSixths.checked_D8_179 i).1 (RealPinwheel.FiveSixths.checked_D8_179 i).2
            rw [← align_19 i]
            have he : 1797 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
