-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_015
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:43:30.347396+00:00
-- url     : https://prove2.me/submissions/108c1da6-7471-4e11-ace6-9191addd9080

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_300
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_301
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_302
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_303
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_304
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_305
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_306
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_307
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_308
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_309
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_310
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_311
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_312
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_313
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_314
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_315
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_316
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_317
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_318
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_319
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
    (hlo : 5415 ≤ j.val) (hhi : j.val < 6561)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 50, codeFunctionP9 (5415 + i.val) = (witnessP9_300 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 51, codeFunctionP9 (5465 + i.val) = (witnessP9_301 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 51, codeFunctionP9 (5516 + i.val) = (witnessP9_302 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 52, codeFunctionP9 (5567 + i.val) = (witnessP9_303 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 53, codeFunctionP9 (5619 + i.val) = (witnessP9_304 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 53, codeFunctionP9 (5672 + i.val) = (witnessP9_305 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 53, codeFunctionP9 (5725 + i.val) = (witnessP9_306 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 55, codeFunctionP9 (5778 + i.val) = (witnessP9_307 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 55, codeFunctionP9 (5833 + i.val) = (witnessP9_308 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 56, codeFunctionP9 (5888 + i.val) = (witnessP9_309 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 57, codeFunctionP9 (5944 + i.val) = (witnessP9_310 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 57, codeFunctionP9 (6001 + i.val) = (witnessP9_311 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 58, codeFunctionP9 (6058 + i.val) = (witnessP9_312 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 59, codeFunctionP9 (6116 + i.val) = (witnessP9_313 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 62, codeFunctionP9 (6175 + i.val) = (witnessP9_314 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 62, codeFunctionP9 (6237 + i.val) = (witnessP9_315 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 62, codeFunctionP9 (6299 + i.val) = (witnessP9_316 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 65, codeFunctionP9 (6361 + i.val) = (witnessP9_317 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 67, codeFunctionP9 (6426 + i.val) = (witnessP9_318 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 68, codeFunctionP9 (6493 + i.val) = (witnessP9_319 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 5944
  ·
    by_cases h0_10 : j.val < 5672
    ·
      by_cases h0_5 : j.val < 5516
      ·
        by_cases h0_2 : j.val < 5465
        ·
          let i : Fin 50 := ⟨j.val - 5415, by omega⟩
          apply of_witness A (witnessP9_300 i) 1800 (RealPinwheel.FiveSixths.checked_P9_300 i).1 (RealPinwheel.FiveSixths.checked_P9_300 i).2
          rw [← align_0 i]
          have he : 5415 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 51 := ⟨j.val - 5465, by omega⟩
          apply of_witness A (witnessP9_301 i) 1800 (RealPinwheel.FiveSixths.checked_P9_301 i).1 (RealPinwheel.FiveSixths.checked_P9_301 i).2
          rw [← align_1 i]
          have he : 5465 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 5567
        ·
          let i : Fin 51 := ⟨j.val - 5516, by omega⟩
          apply of_witness A (witnessP9_302 i) 1800 (RealPinwheel.FiveSixths.checked_P9_302 i).1 (RealPinwheel.FiveSixths.checked_P9_302 i).2
          rw [← align_2 i]
          have he : 5516 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 5619
          ·
            let i : Fin 52 := ⟨j.val - 5567, by omega⟩
            apply of_witness A (witnessP9_303 i) 1800 (RealPinwheel.FiveSixths.checked_P9_303 i).1 (RealPinwheel.FiveSixths.checked_P9_303 i).2
            rw [← align_3 i]
            have he : 5567 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 53 := ⟨j.val - 5619, by omega⟩
            apply of_witness A (witnessP9_304 i) 1800 (RealPinwheel.FiveSixths.checked_P9_304 i).1 (RealPinwheel.FiveSixths.checked_P9_304 i).2
            rw [← align_4 i]
            have he : 5619 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 5778
      ·
        by_cases h5_7 : j.val < 5725
        ·
          let i : Fin 53 := ⟨j.val - 5672, by omega⟩
          apply of_witness A (witnessP9_305 i) 1800 (RealPinwheel.FiveSixths.checked_P9_305 i).1 (RealPinwheel.FiveSixths.checked_P9_305 i).2
          rw [← align_5 i]
          have he : 5672 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 53 := ⟨j.val - 5725, by omega⟩
          apply of_witness A (witnessP9_306 i) 1800 (RealPinwheel.FiveSixths.checked_P9_306 i).1 (RealPinwheel.FiveSixths.checked_P9_306 i).2
          rw [← align_6 i]
          have he : 5725 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 5833
        ·
          let i : Fin 55 := ⟨j.val - 5778, by omega⟩
          apply of_witness A (witnessP9_307 i) 1800 (RealPinwheel.FiveSixths.checked_P9_307 i).1 (RealPinwheel.FiveSixths.checked_P9_307 i).2
          rw [← align_7 i]
          have he : 5778 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 5888
          ·
            let i : Fin 55 := ⟨j.val - 5833, by omega⟩
            apply of_witness A (witnessP9_308 i) 1800 (RealPinwheel.FiveSixths.checked_P9_308 i).1 (RealPinwheel.FiveSixths.checked_P9_308 i).2
            rw [← align_8 i]
            have he : 5833 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 56 := ⟨j.val - 5888, by omega⟩
            apply of_witness A (witnessP9_309 i) 1800 (RealPinwheel.FiveSixths.checked_P9_309 i).1 (RealPinwheel.FiveSixths.checked_P9_309 i).2
            rw [← align_9 i]
            have he : 5888 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 6237
    ·
      by_cases h10_15 : j.val < 6058
      ·
        by_cases h10_12 : j.val < 6001
        ·
          let i : Fin 57 := ⟨j.val - 5944, by omega⟩
          apply of_witness A (witnessP9_310 i) 1800 (RealPinwheel.FiveSixths.checked_P9_310 i).1 (RealPinwheel.FiveSixths.checked_P9_310 i).2
          rw [← align_10 i]
          have he : 5944 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 57 := ⟨j.val - 6001, by omega⟩
          apply of_witness A (witnessP9_311 i) 1800 (RealPinwheel.FiveSixths.checked_P9_311 i).1 (RealPinwheel.FiveSixths.checked_P9_311 i).2
          rw [← align_11 i]
          have he : 6001 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 6116
        ·
          let i : Fin 58 := ⟨j.val - 6058, by omega⟩
          apply of_witness A (witnessP9_312 i) 1800 (RealPinwheel.FiveSixths.checked_P9_312 i).1 (RealPinwheel.FiveSixths.checked_P9_312 i).2
          rw [← align_12 i]
          have he : 6058 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 6175
          ·
            let i : Fin 59 := ⟨j.val - 6116, by omega⟩
            apply of_witness A (witnessP9_313 i) 1800 (RealPinwheel.FiveSixths.checked_P9_313 i).1 (RealPinwheel.FiveSixths.checked_P9_313 i).2
            rw [← align_13 i]
            have he : 6116 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 62 := ⟨j.val - 6175, by omega⟩
            apply of_witness A (witnessP9_314 i) 1800 (RealPinwheel.FiveSixths.checked_P9_314 i).1 (RealPinwheel.FiveSixths.checked_P9_314 i).2
            rw [← align_14 i]
            have he : 6175 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 6361
      ·
        by_cases h15_17 : j.val < 6299
        ·
          let i : Fin 62 := ⟨j.val - 6237, by omega⟩
          apply of_witness A (witnessP9_315 i) 1800 (RealPinwheel.FiveSixths.checked_P9_315 i).1 (RealPinwheel.FiveSixths.checked_P9_315 i).2
          rw [← align_15 i]
          have he : 6237 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 62 := ⟨j.val - 6299, by omega⟩
          apply of_witness A (witnessP9_316 i) 1800 (RealPinwheel.FiveSixths.checked_P9_316 i).1 (RealPinwheel.FiveSixths.checked_P9_316 i).2
          rw [← align_16 i]
          have he : 6299 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 6426
        ·
          let i : Fin 65 := ⟨j.val - 6361, by omega⟩
          apply of_witness A (witnessP9_317 i) 1800 (RealPinwheel.FiveSixths.checked_P9_317 i).1 (RealPinwheel.FiveSixths.checked_P9_317 i).2
          rw [← align_17 i]
          have he : 6361 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 6493
          ·
            let i : Fin 67 := ⟨j.val - 6426, by omega⟩
            apply of_witness A (witnessP9_318 i) 1800 (RealPinwheel.FiveSixths.checked_P9_318 i).1 (RealPinwheel.FiveSixths.checked_P9_318 i).2
            rw [← align_18 i]
            have he : 6426 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 68 := ⟨j.val - 6493, by omega⟩
            apply of_witness A (witnessP9_319 i) 1800 (RealPinwheel.FiveSixths.checked_P9_319 i).1 (RealPinwheel.FiveSixths.checked_P9_319 i).2
            rw [← align_19 i]
            have he : 6493 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
