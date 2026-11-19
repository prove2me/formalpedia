-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_016
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:55:05.178677+00:00
-- url     : https://prove2.me/submissions/da902fe7-2bfb-4d0f-aec4-9bad10312962

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_320
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_321
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_322
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_323
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_324
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_325
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_326
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_327
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_328
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_329
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_330
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_331
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_332
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_333
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_334
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_335
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
    (hlo : 6561 ≤ j.val) (hhi : j.val < 7968)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 70, codeFunctionP9 (6561 + i.val) = (witnessP9_320 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 71, codeFunctionP9 (6631 + i.val) = (witnessP9_321 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 72, codeFunctionP9 (6702 + i.val) = (witnessP9_322 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 75, codeFunctionP9 (6774 + i.val) = (witnessP9_323 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 75, codeFunctionP9 (6849 + i.val) = (witnessP9_324 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 77, codeFunctionP9 (6924 + i.val) = (witnessP9_325 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 79, codeFunctionP9 (7001 + i.val) = (witnessP9_326 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 83, codeFunctionP9 (7080 + i.val) = (witnessP9_327 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 83, codeFunctionP9 (7163 + i.val) = (witnessP9_328 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 87, codeFunctionP9 (7246 + i.val) = (witnessP9_329 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 89, codeFunctionP9 (7333 + i.val) = (witnessP9_330 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 93, codeFunctionP9 (7422 + i.val) = (witnessP9_331 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 99, codeFunctionP9 (7515 + i.val) = (witnessP9_332 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 105, codeFunctionP9 (7614 + i.val) = (witnessP9_333 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 118, codeFunctionP9 (7719 + i.val) = (witnessP9_334 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 131, codeFunctionP9 (7837 + i.val) = (witnessP9_335 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_16 : j.val < 7163
  ·
    by_cases h0_8 : j.val < 6849
    ·
      by_cases h0_4 : j.val < 6702
      ·
        by_cases h0_2 : j.val < 6631
        ·
          let i : Fin 70 := ⟨j.val - 6561, by omega⟩
          apply of_witness A (witnessP9_320 i) 1800 (RealPinwheel.FiveSixths.checked_P9_320 i).1 (RealPinwheel.FiveSixths.checked_P9_320 i).2
          rw [← align_0 i]
          have he : 6561 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 71 := ⟨j.val - 6631, by omega⟩
          apply of_witness A (witnessP9_321 i) 1800 (RealPinwheel.FiveSixths.checked_P9_321 i).1 (RealPinwheel.FiveSixths.checked_P9_321 i).2
          rw [← align_1 i]
          have he : 6631 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_4 : j.val < 6774
        ·
          let i : Fin 72 := ⟨j.val - 6702, by omega⟩
          apply of_witness A (witnessP9_322 i) 1800 (RealPinwheel.FiveSixths.checked_P9_322 i).1 (RealPinwheel.FiveSixths.checked_P9_322 i).2
          rw [← align_2 i]
          have he : 6702 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 75 := ⟨j.val - 6774, by omega⟩
          apply of_witness A (witnessP9_323 i) 1800 (RealPinwheel.FiveSixths.checked_P9_323 i).1 (RealPinwheel.FiveSixths.checked_P9_323 i).2
          rw [← align_3 i]
          have he : 6774 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
    ·
      by_cases h4_8 : j.val < 7001
      ·
        by_cases h4_6 : j.val < 6924
        ·
          let i : Fin 75 := ⟨j.val - 6849, by omega⟩
          apply of_witness A (witnessP9_324 i) 1800 (RealPinwheel.FiveSixths.checked_P9_324 i).1 (RealPinwheel.FiveSixths.checked_P9_324 i).2
          rw [← align_4 i]
          have he : 6849 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 77 := ⟨j.val - 6924, by omega⟩
          apply of_witness A (witnessP9_325 i) 1800 (RealPinwheel.FiveSixths.checked_P9_325 i).1 (RealPinwheel.FiveSixths.checked_P9_325 i).2
          rw [← align_5 i]
          have he : 6924 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h6_8 : j.val < 7080
        ·
          let i : Fin 79 := ⟨j.val - 7001, by omega⟩
          apply of_witness A (witnessP9_326 i) 1800 (RealPinwheel.FiveSixths.checked_P9_326 i).1 (RealPinwheel.FiveSixths.checked_P9_326 i).2
          rw [← align_6 i]
          have he : 7001 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 83 := ⟨j.val - 7080, by omega⟩
          apply of_witness A (witnessP9_327 i) 1800 (RealPinwheel.FiveSixths.checked_P9_327 i).1 (RealPinwheel.FiveSixths.checked_P9_327 i).2
          rw [← align_7 i]
          have he : 7080 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
  ·
    by_cases h8_16 : j.val < 7515
    ·
      by_cases h8_12 : j.val < 7333
      ·
        by_cases h8_10 : j.val < 7246
        ·
          let i : Fin 83 := ⟨j.val - 7163, by omega⟩
          apply of_witness A (witnessP9_328 i) 1800 (RealPinwheel.FiveSixths.checked_P9_328 i).1 (RealPinwheel.FiveSixths.checked_P9_328 i).2
          rw [← align_8 i]
          have he : 7163 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 87 := ⟨j.val - 7246, by omega⟩
          apply of_witness A (witnessP9_329 i) 1800 (RealPinwheel.FiveSixths.checked_P9_329 i).1 (RealPinwheel.FiveSixths.checked_P9_329 i).2
          rw [← align_9 i]
          have he : 7246 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h10_12 : j.val < 7422
        ·
          let i : Fin 89 := ⟨j.val - 7333, by omega⟩
          apply of_witness A (witnessP9_330 i) 1800 (RealPinwheel.FiveSixths.checked_P9_330 i).1 (RealPinwheel.FiveSixths.checked_P9_330 i).2
          rw [← align_10 i]
          have he : 7333 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 93 := ⟨j.val - 7422, by omega⟩
          apply of_witness A (witnessP9_331 i) 1800 (RealPinwheel.FiveSixths.checked_P9_331 i).1 (RealPinwheel.FiveSixths.checked_P9_331 i).2
          rw [← align_11 i]
          have he : 7422 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
    ·
      by_cases h12_16 : j.val < 7719
      ·
        by_cases h12_14 : j.val < 7614
        ·
          let i : Fin 99 := ⟨j.val - 7515, by omega⟩
          apply of_witness A (witnessP9_332 i) 1800 (RealPinwheel.FiveSixths.checked_P9_332 i).1 (RealPinwheel.FiveSixths.checked_P9_332 i).2
          rw [← align_12 i]
          have he : 7515 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 105 := ⟨j.val - 7614, by omega⟩
          apply of_witness A (witnessP9_333 i) 1800 (RealPinwheel.FiveSixths.checked_P9_333 i).1 (RealPinwheel.FiveSixths.checked_P9_333 i).2
          rw [← align_13 i]
          have he : 7614 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h14_16 : j.val < 7837
        ·
          let i : Fin 118 := ⟨j.val - 7719, by omega⟩
          apply of_witness A (witnessP9_334 i) 1800 (RealPinwheel.FiveSixths.checked_P9_334 i).1 (RealPinwheel.FiveSixths.checked_P9_334 i).2
          rw [← align_14 i]
          have he : 7719 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 131 := ⟨j.val - 7837, by omega⟩
          apply of_witness A (witnessP9_335 i) 1800 (RealPinwheel.FiveSixths.checked_P9_335 i).1 (RealPinwheel.FiveSixths.checked_P9_335 i).2
          rw [← align_15 i]
          have he : 7837 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
