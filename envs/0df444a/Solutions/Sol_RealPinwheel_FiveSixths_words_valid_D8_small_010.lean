-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_small_010
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:11:41.131186+00:00
-- url     : https://prove2.me/submissions/8c179d89-11e1-45be-900f-193050c92c15

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_200
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_201
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_202
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_203
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_204
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_205
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_206
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_207
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_208
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_209
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_210
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_211
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_212
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_213
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_214
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_215
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_216
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_217
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_218
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_219
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
    (hlo : 2228 ≤ j.val) (hhi : j.val < 2724)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 23, codeFunctionD8 (2228 + i.val) = (witnessD8_200 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 23, codeFunctionD8 (2251 + i.val) = (witnessD8_201 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 23, codeFunctionD8 (2274 + i.val) = (witnessD8_202 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 23, codeFunctionD8 (2297 + i.val) = (witnessD8_203 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 23, codeFunctionD8 (2320 + i.val) = (witnessD8_204 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 23, codeFunctionD8 (2343 + i.val) = (witnessD8_205 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 24, codeFunctionD8 (2366 + i.val) = (witnessD8_206 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 25, codeFunctionD8 (2390 + i.val) = (witnessD8_207 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 25, codeFunctionD8 (2415 + i.val) = (witnessD8_208 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 25, codeFunctionD8 (2440 + i.val) = (witnessD8_209 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 25, codeFunctionD8 (2465 + i.val) = (witnessD8_210 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 25, codeFunctionD8 (2490 + i.val) = (witnessD8_211 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 25, codeFunctionD8 (2515 + i.val) = (witnessD8_212 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 26, codeFunctionD8 (2540 + i.val) = (witnessD8_213 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 26, codeFunctionD8 (2566 + i.val) = (witnessD8_214 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 26, codeFunctionD8 (2592 + i.val) = (witnessD8_215 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 26, codeFunctionD8 (2618 + i.val) = (witnessD8_216 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 26, codeFunctionD8 (2644 + i.val) = (witnessD8_217 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 27, codeFunctionD8 (2670 + i.val) = (witnessD8_218 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 27, codeFunctionD8 (2697 + i.val) = (witnessD8_219 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 2465
  ·
    by_cases h0_10 : j.val < 2343
    ·
      by_cases h0_5 : j.val < 2274
      ·
        by_cases h0_2 : j.val < 2251
        ·
          let i : Fin 23 := ⟨j.val - 2228, by omega⟩
          apply of_witness A (witnessD8_200 i) 608 (RealPinwheel.FiveSixths.checked_D8_200 i).1 (RealPinwheel.FiveSixths.checked_D8_200 i).2
          rw [← align_0 i]
          have he : 2228 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 23 := ⟨j.val - 2251, by omega⟩
          apply of_witness A (witnessD8_201 i) 608 (RealPinwheel.FiveSixths.checked_D8_201 i).1 (RealPinwheel.FiveSixths.checked_D8_201 i).2
          rw [← align_1 i]
          have he : 2251 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 2297
        ·
          let i : Fin 23 := ⟨j.val - 2274, by omega⟩
          apply of_witness A (witnessD8_202 i) 608 (RealPinwheel.FiveSixths.checked_D8_202 i).1 (RealPinwheel.FiveSixths.checked_D8_202 i).2
          rw [← align_2 i]
          have he : 2274 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 2320
          ·
            let i : Fin 23 := ⟨j.val - 2297, by omega⟩
            apply of_witness A (witnessD8_203 i) 608 (RealPinwheel.FiveSixths.checked_D8_203 i).1 (RealPinwheel.FiveSixths.checked_D8_203 i).2
            rw [← align_3 i]
            have he : 2297 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 23 := ⟨j.val - 2320, by omega⟩
            apply of_witness A (witnessD8_204 i) 608 (RealPinwheel.FiveSixths.checked_D8_204 i).1 (RealPinwheel.FiveSixths.checked_D8_204 i).2
            rw [← align_4 i]
            have he : 2320 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 2390
      ·
        by_cases h5_7 : j.val < 2366
        ·
          let i : Fin 23 := ⟨j.val - 2343, by omega⟩
          apply of_witness A (witnessD8_205 i) 608 (RealPinwheel.FiveSixths.checked_D8_205 i).1 (RealPinwheel.FiveSixths.checked_D8_205 i).2
          rw [← align_5 i]
          have he : 2343 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 24 := ⟨j.val - 2366, by omega⟩
          apply of_witness A (witnessD8_206 i) 608 (RealPinwheel.FiveSixths.checked_D8_206 i).1 (RealPinwheel.FiveSixths.checked_D8_206 i).2
          rw [← align_6 i]
          have he : 2366 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 2415
        ·
          let i : Fin 25 := ⟨j.val - 2390, by omega⟩
          apply of_witness A (witnessD8_207 i) 608 (RealPinwheel.FiveSixths.checked_D8_207 i).1 (RealPinwheel.FiveSixths.checked_D8_207 i).2
          rw [← align_7 i]
          have he : 2390 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 2440
          ·
            let i : Fin 25 := ⟨j.val - 2415, by omega⟩
            apply of_witness A (witnessD8_208 i) 608 (RealPinwheel.FiveSixths.checked_D8_208 i).1 (RealPinwheel.FiveSixths.checked_D8_208 i).2
            rw [← align_8 i]
            have he : 2415 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 25 := ⟨j.val - 2440, by omega⟩
            apply of_witness A (witnessD8_209 i) 608 (RealPinwheel.FiveSixths.checked_D8_209 i).1 (RealPinwheel.FiveSixths.checked_D8_209 i).2
            rw [← align_9 i]
            have he : 2440 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 2592
    ·
      by_cases h10_15 : j.val < 2515
      ·
        by_cases h10_12 : j.val < 2490
        ·
          let i : Fin 25 := ⟨j.val - 2465, by omega⟩
          apply of_witness A (witnessD8_210 i) 608 (RealPinwheel.FiveSixths.checked_D8_210 i).1 (RealPinwheel.FiveSixths.checked_D8_210 i).2
          rw [← align_10 i]
          have he : 2465 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 25 := ⟨j.val - 2490, by omega⟩
          apply of_witness A (witnessD8_211 i) 608 (RealPinwheel.FiveSixths.checked_D8_211 i).1 (RealPinwheel.FiveSixths.checked_D8_211 i).2
          rw [← align_11 i]
          have he : 2490 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 2540
        ·
          let i : Fin 25 := ⟨j.val - 2515, by omega⟩
          apply of_witness A (witnessD8_212 i) 608 (RealPinwheel.FiveSixths.checked_D8_212 i).1 (RealPinwheel.FiveSixths.checked_D8_212 i).2
          rw [← align_12 i]
          have he : 2515 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 2566
          ·
            let i : Fin 26 := ⟨j.val - 2540, by omega⟩
            apply of_witness A (witnessD8_213 i) 608 (RealPinwheel.FiveSixths.checked_D8_213 i).1 (RealPinwheel.FiveSixths.checked_D8_213 i).2
            rw [← align_13 i]
            have he : 2540 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 26 := ⟨j.val - 2566, by omega⟩
            apply of_witness A (witnessD8_214 i) 608 (RealPinwheel.FiveSixths.checked_D8_214 i).1 (RealPinwheel.FiveSixths.checked_D8_214 i).2
            rw [← align_14 i]
            have he : 2566 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 2644
      ·
        by_cases h15_17 : j.val < 2618
        ·
          let i : Fin 26 := ⟨j.val - 2592, by omega⟩
          apply of_witness A (witnessD8_215 i) 608 (RealPinwheel.FiveSixths.checked_D8_215 i).1 (RealPinwheel.FiveSixths.checked_D8_215 i).2
          rw [← align_15 i]
          have he : 2592 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 26 := ⟨j.val - 2618, by omega⟩
          apply of_witness A (witnessD8_216 i) 608 (RealPinwheel.FiveSixths.checked_D8_216 i).1 (RealPinwheel.FiveSixths.checked_D8_216 i).2
          rw [← align_16 i]
          have he : 2618 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 2670
        ·
          let i : Fin 26 := ⟨j.val - 2644, by omega⟩
          apply of_witness A (witnessD8_217 i) 608 (RealPinwheel.FiveSixths.checked_D8_217 i).1 (RealPinwheel.FiveSixths.checked_D8_217 i).2
          rw [← align_17 i]
          have he : 2644 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 2697
          ·
            let i : Fin 27 := ⟨j.val - 2670, by omega⟩
            apply of_witness A (witnessD8_218 i) 608 (RealPinwheel.FiveSixths.checked_D8_218 i).1 (RealPinwheel.FiveSixths.checked_D8_218 i).2
            rw [← align_18 i]
            have he : 2670 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 27 := ⟨j.val - 2697, by omega⟩
            apply of_witness A (witnessD8_219 i) 608 (RealPinwheel.FiveSixths.checked_D8_219 i).1 (RealPinwheel.FiveSixths.checked_D8_219 i).2
            rw [← align_19 i]
            have he : 2697 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
