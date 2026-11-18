-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_002
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:50:40.86538+00:00
-- url     : https://prove2.me/submissions/a0464521-4b0c-4d93-b257-e2f4d2670be9

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_040
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_041
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_042
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_043
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_044
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_045
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_046
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_047
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_048
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_049
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_050
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_051
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_052
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_053
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_054
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_055
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_056
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_057
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_058
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_059
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
    (hlo : 113 ≤ j.val) (hhi : j.val < 223)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 5, codeFunctionP9 (113 + i.val) = (witnessP9_040 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 5, codeFunctionP9 (118 + i.val) = (witnessP9_041 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 5, codeFunctionP9 (123 + i.val) = (witnessP9_042 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 5, codeFunctionP9 (128 + i.val) = (witnessP9_043 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 5, codeFunctionP9 (133 + i.val) = (witnessP9_044 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 5, codeFunctionP9 (138 + i.val) = (witnessP9_045 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 5, codeFunctionP9 (143 + i.val) = (witnessP9_046 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 5, codeFunctionP9 (148 + i.val) = (witnessP9_047 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 5, codeFunctionP9 (153 + i.val) = (witnessP9_048 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 5, codeFunctionP9 (158 + i.val) = (witnessP9_049 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 6, codeFunctionP9 (163 + i.val) = (witnessP9_050 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 6, codeFunctionP9 (169 + i.val) = (witnessP9_051 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 6, codeFunctionP9 (175 + i.val) = (witnessP9_052 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 6, codeFunctionP9 (181 + i.val) = (witnessP9_053 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 6, codeFunctionP9 (187 + i.val) = (witnessP9_054 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 6, codeFunctionP9 (193 + i.val) = (witnessP9_055 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 6, codeFunctionP9 (199 + i.val) = (witnessP9_056 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 6, codeFunctionP9 (205 + i.val) = (witnessP9_057 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 6, codeFunctionP9 (211 + i.val) = (witnessP9_058 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 6, codeFunctionP9 (217 + i.val) = (witnessP9_059 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 163
  ·
    by_cases h0_10 : j.val < 138
    ·
      by_cases h0_5 : j.val < 123
      ·
        by_cases h0_2 : j.val < 118
        ·
          let i : Fin 5 := ⟨j.val - 113, by omega⟩
          apply of_witness A (witnessP9_040 i) 1800 (RealPinwheel.FiveSixths.checked_P9_040 i).1 (RealPinwheel.FiveSixths.checked_P9_040 i).2
          rw [← align_0 i]
          have he : 113 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 5 := ⟨j.val - 118, by omega⟩
          apply of_witness A (witnessP9_041 i) 1800 (RealPinwheel.FiveSixths.checked_P9_041 i).1 (RealPinwheel.FiveSixths.checked_P9_041 i).2
          rw [← align_1 i]
          have he : 118 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 128
        ·
          let i : Fin 5 := ⟨j.val - 123, by omega⟩
          apply of_witness A (witnessP9_042 i) 1800 (RealPinwheel.FiveSixths.checked_P9_042 i).1 (RealPinwheel.FiveSixths.checked_P9_042 i).2
          rw [← align_2 i]
          have he : 123 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 133
          ·
            let i : Fin 5 := ⟨j.val - 128, by omega⟩
            apply of_witness A (witnessP9_043 i) 1800 (RealPinwheel.FiveSixths.checked_P9_043 i).1 (RealPinwheel.FiveSixths.checked_P9_043 i).2
            rw [← align_3 i]
            have he : 128 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 5 := ⟨j.val - 133, by omega⟩
            apply of_witness A (witnessP9_044 i) 1800 (RealPinwheel.FiveSixths.checked_P9_044 i).1 (RealPinwheel.FiveSixths.checked_P9_044 i).2
            rw [← align_4 i]
            have he : 133 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 148
      ·
        by_cases h5_7 : j.val < 143
        ·
          let i : Fin 5 := ⟨j.val - 138, by omega⟩
          apply of_witness A (witnessP9_045 i) 1800 (RealPinwheel.FiveSixths.checked_P9_045 i).1 (RealPinwheel.FiveSixths.checked_P9_045 i).2
          rw [← align_5 i]
          have he : 138 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 5 := ⟨j.val - 143, by omega⟩
          apply of_witness A (witnessP9_046 i) 1800 (RealPinwheel.FiveSixths.checked_P9_046 i).1 (RealPinwheel.FiveSixths.checked_P9_046 i).2
          rw [← align_6 i]
          have he : 143 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 153
        ·
          let i : Fin 5 := ⟨j.val - 148, by omega⟩
          apply of_witness A (witnessP9_047 i) 1800 (RealPinwheel.FiveSixths.checked_P9_047 i).1 (RealPinwheel.FiveSixths.checked_P9_047 i).2
          rw [← align_7 i]
          have he : 148 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 158
          ·
            let i : Fin 5 := ⟨j.val - 153, by omega⟩
            apply of_witness A (witnessP9_048 i) 1800 (RealPinwheel.FiveSixths.checked_P9_048 i).1 (RealPinwheel.FiveSixths.checked_P9_048 i).2
            rw [← align_8 i]
            have he : 153 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 5 := ⟨j.val - 158, by omega⟩
            apply of_witness A (witnessP9_049 i) 1800 (RealPinwheel.FiveSixths.checked_P9_049 i).1 (RealPinwheel.FiveSixths.checked_P9_049 i).2
            rw [← align_9 i]
            have he : 158 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 193
    ·
      by_cases h10_15 : j.val < 175
      ·
        by_cases h10_12 : j.val < 169
        ·
          let i : Fin 6 := ⟨j.val - 163, by omega⟩
          apply of_witness A (witnessP9_050 i) 1800 (RealPinwheel.FiveSixths.checked_P9_050 i).1 (RealPinwheel.FiveSixths.checked_P9_050 i).2
          rw [← align_10 i]
          have he : 163 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 6 := ⟨j.val - 169, by omega⟩
          apply of_witness A (witnessP9_051 i) 1800 (RealPinwheel.FiveSixths.checked_P9_051 i).1 (RealPinwheel.FiveSixths.checked_P9_051 i).2
          rw [← align_11 i]
          have he : 169 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 181
        ·
          let i : Fin 6 := ⟨j.val - 175, by omega⟩
          apply of_witness A (witnessP9_052 i) 1800 (RealPinwheel.FiveSixths.checked_P9_052 i).1 (RealPinwheel.FiveSixths.checked_P9_052 i).2
          rw [← align_12 i]
          have he : 175 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 187
          ·
            let i : Fin 6 := ⟨j.val - 181, by omega⟩
            apply of_witness A (witnessP9_053 i) 1800 (RealPinwheel.FiveSixths.checked_P9_053 i).1 (RealPinwheel.FiveSixths.checked_P9_053 i).2
            rw [← align_13 i]
            have he : 181 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 6 := ⟨j.val - 187, by omega⟩
            apply of_witness A (witnessP9_054 i) 1800 (RealPinwheel.FiveSixths.checked_P9_054 i).1 (RealPinwheel.FiveSixths.checked_P9_054 i).2
            rw [← align_14 i]
            have he : 187 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 205
      ·
        by_cases h15_17 : j.val < 199
        ·
          let i : Fin 6 := ⟨j.val - 193, by omega⟩
          apply of_witness A (witnessP9_055 i) 1800 (RealPinwheel.FiveSixths.checked_P9_055 i).1 (RealPinwheel.FiveSixths.checked_P9_055 i).2
          rw [← align_15 i]
          have he : 193 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 6 := ⟨j.val - 199, by omega⟩
          apply of_witness A (witnessP9_056 i) 1800 (RealPinwheel.FiveSixths.checked_P9_056 i).1 (RealPinwheel.FiveSixths.checked_P9_056 i).2
          rw [← align_16 i]
          have he : 199 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 211
        ·
          let i : Fin 6 := ⟨j.val - 205, by omega⟩
          apply of_witness A (witnessP9_057 i) 1800 (RealPinwheel.FiveSixths.checked_P9_057 i).1 (RealPinwheel.FiveSixths.checked_P9_057 i).2
          rw [← align_17 i]
          have he : 205 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 217
          ·
            let i : Fin 6 := ⟨j.val - 211, by omega⟩
            apply of_witness A (witnessP9_058 i) 1800 (RealPinwheel.FiveSixths.checked_P9_058 i).1 (RealPinwheel.FiveSixths.checked_P9_058 i).2
            rw [← align_18 i]
            have he : 211 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 6 := ⟨j.val - 217, by omega⟩
            apply of_witness A (witnessP9_059 i) 1800 (RealPinwheel.FiveSixths.checked_P9_059 i).1 (RealPinwheel.FiveSixths.checked_P9_059 i).2
            rw [← align_19 i]
            have he : 217 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
