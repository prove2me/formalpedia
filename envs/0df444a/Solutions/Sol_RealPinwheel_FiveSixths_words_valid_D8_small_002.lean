-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_small_002
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:27:26.33366+00:00
-- url     : https://prove2.me/submissions/a74bef50-4c55-4178-9f04-07552aa86fea

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_040
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_041
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_042
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_043
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_044
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_045
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_046
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_047
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_048
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_049
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_050
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_051
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_052
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_053
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_054
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_055
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_056
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_057
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_058
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_059
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
    (hlo : 152 ≤ j.val) (hhi : j.val < 287)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 6, codeFunctionD8 (152 + i.val) = (witnessD8_040 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 6, codeFunctionD8 (158 + i.val) = (witnessD8_041 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 6, codeFunctionD8 (164 + i.val) = (witnessD8_042 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 6, codeFunctionD8 (170 + i.val) = (witnessD8_043 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 6, codeFunctionD8 (176 + i.val) = (witnessD8_044 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 6, codeFunctionD8 (182 + i.val) = (witnessD8_045 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 6, codeFunctionD8 (188 + i.val) = (witnessD8_046 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 7, codeFunctionD8 (194 + i.val) = (witnessD8_047 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 7, codeFunctionD8 (201 + i.val) = (witnessD8_048 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 7, codeFunctionD8 (208 + i.val) = (witnessD8_049 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 7, codeFunctionD8 (215 + i.val) = (witnessD8_050 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 7, codeFunctionD8 (222 + i.val) = (witnessD8_051 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 7, codeFunctionD8 (229 + i.val) = (witnessD8_052 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 7, codeFunctionD8 (236 + i.val) = (witnessD8_053 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 7, codeFunctionD8 (243 + i.val) = (witnessD8_054 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 7, codeFunctionD8 (250 + i.val) = (witnessD8_055 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 7, codeFunctionD8 (257 + i.val) = (witnessD8_056 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 7, codeFunctionD8 (264 + i.val) = (witnessD8_057 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 8, codeFunctionD8 (271 + i.val) = (witnessD8_058 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 8, codeFunctionD8 (279 + i.val) = (witnessD8_059 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 215
  ·
    by_cases h0_10 : j.val < 182
    ·
      by_cases h0_5 : j.val < 164
      ·
        by_cases h0_2 : j.val < 158
        ·
          let i : Fin 6 := ⟨j.val - 152, by omega⟩
          apply of_witness A (witnessD8_040 i) 608 (RealPinwheel.FiveSixths.checked_D8_040 i).1 (RealPinwheel.FiveSixths.checked_D8_040 i).2
          rw [← align_0 i]
          have he : 152 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 6 := ⟨j.val - 158, by omega⟩
          apply of_witness A (witnessD8_041 i) 608 (RealPinwheel.FiveSixths.checked_D8_041 i).1 (RealPinwheel.FiveSixths.checked_D8_041 i).2
          rw [← align_1 i]
          have he : 158 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 170
        ·
          let i : Fin 6 := ⟨j.val - 164, by omega⟩
          apply of_witness A (witnessD8_042 i) 608 (RealPinwheel.FiveSixths.checked_D8_042 i).1 (RealPinwheel.FiveSixths.checked_D8_042 i).2
          rw [← align_2 i]
          have he : 164 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 176
          ·
            let i : Fin 6 := ⟨j.val - 170, by omega⟩
            apply of_witness A (witnessD8_043 i) 608 (RealPinwheel.FiveSixths.checked_D8_043 i).1 (RealPinwheel.FiveSixths.checked_D8_043 i).2
            rw [← align_3 i]
            have he : 170 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 6 := ⟨j.val - 176, by omega⟩
            apply of_witness A (witnessD8_044 i) 608 (RealPinwheel.FiveSixths.checked_D8_044 i).1 (RealPinwheel.FiveSixths.checked_D8_044 i).2
            rw [← align_4 i]
            have he : 176 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 194
      ·
        by_cases h5_7 : j.val < 188
        ·
          let i : Fin 6 := ⟨j.val - 182, by omega⟩
          apply of_witness A (witnessD8_045 i) 608 (RealPinwheel.FiveSixths.checked_D8_045 i).1 (RealPinwheel.FiveSixths.checked_D8_045 i).2
          rw [← align_5 i]
          have he : 182 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 6 := ⟨j.val - 188, by omega⟩
          apply of_witness A (witnessD8_046 i) 608 (RealPinwheel.FiveSixths.checked_D8_046 i).1 (RealPinwheel.FiveSixths.checked_D8_046 i).2
          rw [← align_6 i]
          have he : 188 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 201
        ·
          let i : Fin 7 := ⟨j.val - 194, by omega⟩
          apply of_witness A (witnessD8_047 i) 608 (RealPinwheel.FiveSixths.checked_D8_047 i).1 (RealPinwheel.FiveSixths.checked_D8_047 i).2
          rw [← align_7 i]
          have he : 194 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 208
          ·
            let i : Fin 7 := ⟨j.val - 201, by omega⟩
            apply of_witness A (witnessD8_048 i) 608 (RealPinwheel.FiveSixths.checked_D8_048 i).1 (RealPinwheel.FiveSixths.checked_D8_048 i).2
            rw [← align_8 i]
            have he : 201 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 7 := ⟨j.val - 208, by omega⟩
            apply of_witness A (witnessD8_049 i) 608 (RealPinwheel.FiveSixths.checked_D8_049 i).1 (RealPinwheel.FiveSixths.checked_D8_049 i).2
            rw [← align_9 i]
            have he : 208 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 250
    ·
      by_cases h10_15 : j.val < 229
      ·
        by_cases h10_12 : j.val < 222
        ·
          let i : Fin 7 := ⟨j.val - 215, by omega⟩
          apply of_witness A (witnessD8_050 i) 608 (RealPinwheel.FiveSixths.checked_D8_050 i).1 (RealPinwheel.FiveSixths.checked_D8_050 i).2
          rw [← align_10 i]
          have he : 215 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 7 := ⟨j.val - 222, by omega⟩
          apply of_witness A (witnessD8_051 i) 608 (RealPinwheel.FiveSixths.checked_D8_051 i).1 (RealPinwheel.FiveSixths.checked_D8_051 i).2
          rw [← align_11 i]
          have he : 222 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 236
        ·
          let i : Fin 7 := ⟨j.val - 229, by omega⟩
          apply of_witness A (witnessD8_052 i) 608 (RealPinwheel.FiveSixths.checked_D8_052 i).1 (RealPinwheel.FiveSixths.checked_D8_052 i).2
          rw [← align_12 i]
          have he : 229 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 243
          ·
            let i : Fin 7 := ⟨j.val - 236, by omega⟩
            apply of_witness A (witnessD8_053 i) 608 (RealPinwheel.FiveSixths.checked_D8_053 i).1 (RealPinwheel.FiveSixths.checked_D8_053 i).2
            rw [← align_13 i]
            have he : 236 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 7 := ⟨j.val - 243, by omega⟩
            apply of_witness A (witnessD8_054 i) 608 (RealPinwheel.FiveSixths.checked_D8_054 i).1 (RealPinwheel.FiveSixths.checked_D8_054 i).2
            rw [← align_14 i]
            have he : 243 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 264
      ·
        by_cases h15_17 : j.val < 257
        ·
          let i : Fin 7 := ⟨j.val - 250, by omega⟩
          apply of_witness A (witnessD8_055 i) 608 (RealPinwheel.FiveSixths.checked_D8_055 i).1 (RealPinwheel.FiveSixths.checked_D8_055 i).2
          rw [← align_15 i]
          have he : 250 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 7 := ⟨j.val - 257, by omega⟩
          apply of_witness A (witnessD8_056 i) 608 (RealPinwheel.FiveSixths.checked_D8_056 i).1 (RealPinwheel.FiveSixths.checked_D8_056 i).2
          rw [← align_16 i]
          have he : 257 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 271
        ·
          let i : Fin 7 := ⟨j.val - 264, by omega⟩
          apply of_witness A (witnessD8_057 i) 608 (RealPinwheel.FiveSixths.checked_D8_057 i).1 (RealPinwheel.FiveSixths.checked_D8_057 i).2
          rw [← align_17 i]
          have he : 264 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 279
          ·
            let i : Fin 8 := ⟨j.val - 271, by omega⟩
            apply of_witness A (witnessD8_058 i) 608 (RealPinwheel.FiveSixths.checked_D8_058 i).1 (RealPinwheel.FiveSixths.checked_D8_058 i).2
            rw [← align_18 i]
            have he : 271 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 8 := ⟨j.val - 279, by omega⟩
            apply of_witness A (witnessD8_059 i) 608 (RealPinwheel.FiveSixths.checked_D8_059 i).1 (RealPinwheel.FiveSixths.checked_D8_059 i).2
            rw [← align_19 i]
            have he : 279 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
