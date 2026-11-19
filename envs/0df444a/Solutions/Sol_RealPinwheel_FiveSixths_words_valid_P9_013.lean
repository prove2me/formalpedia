-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_013
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:21:08.158318+00:00
-- url     : https://prove2.me/submissions/a9d4471c-713e-4547-9728-54efc88e3d26

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_260
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_261
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_262
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_263
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_264
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_265
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_266
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_267
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_268
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_269
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_270
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_271
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_272
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_273
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_274
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_275
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_276
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_277
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_278
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_279
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
    (hlo : 3756 ≤ j.val) (hhi : j.val < 4511)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 35, codeFunctionP9 (3756 + i.val) = (witnessP9_260 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 35, codeFunctionP9 (3791 + i.val) = (witnessP9_261 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 35, codeFunctionP9 (3826 + i.val) = (witnessP9_262 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 35, codeFunctionP9 (3861 + i.val) = (witnessP9_263 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 36, codeFunctionP9 (3896 + i.val) = (witnessP9_264 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 37, codeFunctionP9 (3932 + i.val) = (witnessP9_265 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 37, codeFunctionP9 (3969 + i.val) = (witnessP9_266 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 37, codeFunctionP9 (4006 + i.val) = (witnessP9_267 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 37, codeFunctionP9 (4043 + i.val) = (witnessP9_268 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 38, codeFunctionP9 (4080 + i.val) = (witnessP9_269 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 38, codeFunctionP9 (4118 + i.val) = (witnessP9_270 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 38, codeFunctionP9 (4156 + i.val) = (witnessP9_271 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 38, codeFunctionP9 (4194 + i.val) = (witnessP9_272 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 39, codeFunctionP9 (4232 + i.val) = (witnessP9_273 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 39, codeFunctionP9 (4271 + i.val) = (witnessP9_274 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 39, codeFunctionP9 (4310 + i.val) = (witnessP9_275 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 39, codeFunctionP9 (4349 + i.val) = (witnessP9_276 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 41, codeFunctionP9 (4388 + i.val) = (witnessP9_277 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 41, codeFunctionP9 (4429 + i.val) = (witnessP9_278 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 41, codeFunctionP9 (4470 + i.val) = (witnessP9_279 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 4118
  ·
    by_cases h0_10 : j.val < 3932
    ·
      by_cases h0_5 : j.val < 3826
      ·
        by_cases h0_2 : j.val < 3791
        ·
          let i : Fin 35 := ⟨j.val - 3756, by omega⟩
          apply of_witness A (witnessP9_260 i) 1800 (RealPinwheel.FiveSixths.checked_P9_260 i).1 (RealPinwheel.FiveSixths.checked_P9_260 i).2
          rw [← align_0 i]
          have he : 3756 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 35 := ⟨j.val - 3791, by omega⟩
          apply of_witness A (witnessP9_261 i) 1800 (RealPinwheel.FiveSixths.checked_P9_261 i).1 (RealPinwheel.FiveSixths.checked_P9_261 i).2
          rw [← align_1 i]
          have he : 3791 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 3861
        ·
          let i : Fin 35 := ⟨j.val - 3826, by omega⟩
          apply of_witness A (witnessP9_262 i) 1800 (RealPinwheel.FiveSixths.checked_P9_262 i).1 (RealPinwheel.FiveSixths.checked_P9_262 i).2
          rw [← align_2 i]
          have he : 3826 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 3896
          ·
            let i : Fin 35 := ⟨j.val - 3861, by omega⟩
            apply of_witness A (witnessP9_263 i) 1800 (RealPinwheel.FiveSixths.checked_P9_263 i).1 (RealPinwheel.FiveSixths.checked_P9_263 i).2
            rw [← align_3 i]
            have he : 3861 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 36 := ⟨j.val - 3896, by omega⟩
            apply of_witness A (witnessP9_264 i) 1800 (RealPinwheel.FiveSixths.checked_P9_264 i).1 (RealPinwheel.FiveSixths.checked_P9_264 i).2
            rw [← align_4 i]
            have he : 3896 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 4006
      ·
        by_cases h5_7 : j.val < 3969
        ·
          let i : Fin 37 := ⟨j.val - 3932, by omega⟩
          apply of_witness A (witnessP9_265 i) 1800 (RealPinwheel.FiveSixths.checked_P9_265 i).1 (RealPinwheel.FiveSixths.checked_P9_265 i).2
          rw [← align_5 i]
          have he : 3932 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 37 := ⟨j.val - 3969, by omega⟩
          apply of_witness A (witnessP9_266 i) 1800 (RealPinwheel.FiveSixths.checked_P9_266 i).1 (RealPinwheel.FiveSixths.checked_P9_266 i).2
          rw [← align_6 i]
          have he : 3969 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 4043
        ·
          let i : Fin 37 := ⟨j.val - 4006, by omega⟩
          apply of_witness A (witnessP9_267 i) 1800 (RealPinwheel.FiveSixths.checked_P9_267 i).1 (RealPinwheel.FiveSixths.checked_P9_267 i).2
          rw [← align_7 i]
          have he : 4006 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 4080
          ·
            let i : Fin 37 := ⟨j.val - 4043, by omega⟩
            apply of_witness A (witnessP9_268 i) 1800 (RealPinwheel.FiveSixths.checked_P9_268 i).1 (RealPinwheel.FiveSixths.checked_P9_268 i).2
            rw [← align_8 i]
            have he : 4043 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 38 := ⟨j.val - 4080, by omega⟩
            apply of_witness A (witnessP9_269 i) 1800 (RealPinwheel.FiveSixths.checked_P9_269 i).1 (RealPinwheel.FiveSixths.checked_P9_269 i).2
            rw [← align_9 i]
            have he : 4080 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 4310
    ·
      by_cases h10_15 : j.val < 4194
      ·
        by_cases h10_12 : j.val < 4156
        ·
          let i : Fin 38 := ⟨j.val - 4118, by omega⟩
          apply of_witness A (witnessP9_270 i) 1800 (RealPinwheel.FiveSixths.checked_P9_270 i).1 (RealPinwheel.FiveSixths.checked_P9_270 i).2
          rw [← align_10 i]
          have he : 4118 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 38 := ⟨j.val - 4156, by omega⟩
          apply of_witness A (witnessP9_271 i) 1800 (RealPinwheel.FiveSixths.checked_P9_271 i).1 (RealPinwheel.FiveSixths.checked_P9_271 i).2
          rw [← align_11 i]
          have he : 4156 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 4232
        ·
          let i : Fin 38 := ⟨j.val - 4194, by omega⟩
          apply of_witness A (witnessP9_272 i) 1800 (RealPinwheel.FiveSixths.checked_P9_272 i).1 (RealPinwheel.FiveSixths.checked_P9_272 i).2
          rw [← align_12 i]
          have he : 4194 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 4271
          ·
            let i : Fin 39 := ⟨j.val - 4232, by omega⟩
            apply of_witness A (witnessP9_273 i) 1800 (RealPinwheel.FiveSixths.checked_P9_273 i).1 (RealPinwheel.FiveSixths.checked_P9_273 i).2
            rw [← align_13 i]
            have he : 4232 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 39 := ⟨j.val - 4271, by omega⟩
            apply of_witness A (witnessP9_274 i) 1800 (RealPinwheel.FiveSixths.checked_P9_274 i).1 (RealPinwheel.FiveSixths.checked_P9_274 i).2
            rw [← align_14 i]
            have he : 4271 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 4388
      ·
        by_cases h15_17 : j.val < 4349
        ·
          let i : Fin 39 := ⟨j.val - 4310, by omega⟩
          apply of_witness A (witnessP9_275 i) 1800 (RealPinwheel.FiveSixths.checked_P9_275 i).1 (RealPinwheel.FiveSixths.checked_P9_275 i).2
          rw [← align_15 i]
          have he : 4310 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 39 := ⟨j.val - 4349, by omega⟩
          apply of_witness A (witnessP9_276 i) 1800 (RealPinwheel.FiveSixths.checked_P9_276 i).1 (RealPinwheel.FiveSixths.checked_P9_276 i).2
          rw [← align_16 i]
          have he : 4349 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 4429
        ·
          let i : Fin 41 := ⟨j.val - 4388, by omega⟩
          apply of_witness A (witnessP9_277 i) 1800 (RealPinwheel.FiveSixths.checked_P9_277 i).1 (RealPinwheel.FiveSixths.checked_P9_277 i).2
          rw [← align_17 i]
          have he : 4388 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 4470
          ·
            let i : Fin 41 := ⟨j.val - 4429, by omega⟩
            apply of_witness A (witnessP9_278 i) 1800 (RealPinwheel.FiveSixths.checked_P9_278 i).1 (RealPinwheel.FiveSixths.checked_P9_278 i).2
            rw [← align_18 i]
            have he : 4429 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 41 := ⟨j.val - 4470, by omega⟩
            apply of_witness A (witnessP9_279 i) 1800 (RealPinwheel.FiveSixths.checked_P9_279 i).1 (RealPinwheel.FiveSixths.checked_P9_279 i).2
            rw [← align_19 i]
            have he : 4470 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
