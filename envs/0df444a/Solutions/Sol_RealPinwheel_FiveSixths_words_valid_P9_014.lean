-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_014
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:33:02.274093+00:00
-- url     : https://prove2.me/submissions/99349ef9-5049-4619-870d-dd82d7068e01

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_280
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_281
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_282
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_283
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_284
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_285
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_286
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_287
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_288
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_289
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_290
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_291
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_292
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_293
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_294
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_295
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_296
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_297
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_298
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_299
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
    (hlo : 4511 ≤ j.val) (hhi : j.val < 5415)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 41, codeFunctionP9 (4511 + i.val) = (witnessP9_280 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 41, codeFunctionP9 (4552 + i.val) = (witnessP9_281 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 41, codeFunctionP9 (4593 + i.val) = (witnessP9_282 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 42, codeFunctionP9 (4634 + i.val) = (witnessP9_283 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 43, codeFunctionP9 (4676 + i.val) = (witnessP9_284 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 44, codeFunctionP9 (4719 + i.val) = (witnessP9_285 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 44, codeFunctionP9 (4763 + i.val) = (witnessP9_286 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 44, codeFunctionP9 (4807 + i.val) = (witnessP9_287 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 44, codeFunctionP9 (4851 + i.val) = (witnessP9_288 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 45, codeFunctionP9 (4895 + i.val) = (witnessP9_289 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 45, codeFunctionP9 (4940 + i.val) = (witnessP9_290 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 46, codeFunctionP9 (4985 + i.val) = (witnessP9_291 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 46, codeFunctionP9 (5031 + i.val) = (witnessP9_292 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 46, codeFunctionP9 (5077 + i.val) = (witnessP9_293 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 46, codeFunctionP9 (5123 + i.val) = (witnessP9_294 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 47, codeFunctionP9 (5169 + i.val) = (witnessP9_295 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 49, codeFunctionP9 (5216 + i.val) = (witnessP9_296 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 50, codeFunctionP9 (5265 + i.val) = (witnessP9_297 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 50, codeFunctionP9 (5315 + i.val) = (witnessP9_298 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 50, codeFunctionP9 (5365 + i.val) = (witnessP9_299 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 4940
  ·
    by_cases h0_10 : j.val < 4719
    ·
      by_cases h0_5 : j.val < 4593
      ·
        by_cases h0_2 : j.val < 4552
        ·
          let i : Fin 41 := ⟨j.val - 4511, by omega⟩
          apply of_witness A (witnessP9_280 i) 1800 (RealPinwheel.FiveSixths.checked_P9_280 i).1 (RealPinwheel.FiveSixths.checked_P9_280 i).2
          rw [← align_0 i]
          have he : 4511 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 41 := ⟨j.val - 4552, by omega⟩
          apply of_witness A (witnessP9_281 i) 1800 (RealPinwheel.FiveSixths.checked_P9_281 i).1 (RealPinwheel.FiveSixths.checked_P9_281 i).2
          rw [← align_1 i]
          have he : 4552 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 4634
        ·
          let i : Fin 41 := ⟨j.val - 4593, by omega⟩
          apply of_witness A (witnessP9_282 i) 1800 (RealPinwheel.FiveSixths.checked_P9_282 i).1 (RealPinwheel.FiveSixths.checked_P9_282 i).2
          rw [← align_2 i]
          have he : 4593 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 4676
          ·
            let i : Fin 42 := ⟨j.val - 4634, by omega⟩
            apply of_witness A (witnessP9_283 i) 1800 (RealPinwheel.FiveSixths.checked_P9_283 i).1 (RealPinwheel.FiveSixths.checked_P9_283 i).2
            rw [← align_3 i]
            have he : 4634 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 43 := ⟨j.val - 4676, by omega⟩
            apply of_witness A (witnessP9_284 i) 1800 (RealPinwheel.FiveSixths.checked_P9_284 i).1 (RealPinwheel.FiveSixths.checked_P9_284 i).2
            rw [← align_4 i]
            have he : 4676 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 4807
      ·
        by_cases h5_7 : j.val < 4763
        ·
          let i : Fin 44 := ⟨j.val - 4719, by omega⟩
          apply of_witness A (witnessP9_285 i) 1800 (RealPinwheel.FiveSixths.checked_P9_285 i).1 (RealPinwheel.FiveSixths.checked_P9_285 i).2
          rw [← align_5 i]
          have he : 4719 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 44 := ⟨j.val - 4763, by omega⟩
          apply of_witness A (witnessP9_286 i) 1800 (RealPinwheel.FiveSixths.checked_P9_286 i).1 (RealPinwheel.FiveSixths.checked_P9_286 i).2
          rw [← align_6 i]
          have he : 4763 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 4851
        ·
          let i : Fin 44 := ⟨j.val - 4807, by omega⟩
          apply of_witness A (witnessP9_287 i) 1800 (RealPinwheel.FiveSixths.checked_P9_287 i).1 (RealPinwheel.FiveSixths.checked_P9_287 i).2
          rw [← align_7 i]
          have he : 4807 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 4895
          ·
            let i : Fin 44 := ⟨j.val - 4851, by omega⟩
            apply of_witness A (witnessP9_288 i) 1800 (RealPinwheel.FiveSixths.checked_P9_288 i).1 (RealPinwheel.FiveSixths.checked_P9_288 i).2
            rw [← align_8 i]
            have he : 4851 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 45 := ⟨j.val - 4895, by omega⟩
            apply of_witness A (witnessP9_289 i) 1800 (RealPinwheel.FiveSixths.checked_P9_289 i).1 (RealPinwheel.FiveSixths.checked_P9_289 i).2
            rw [← align_9 i]
            have he : 4895 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 5169
    ·
      by_cases h10_15 : j.val < 5031
      ·
        by_cases h10_12 : j.val < 4985
        ·
          let i : Fin 45 := ⟨j.val - 4940, by omega⟩
          apply of_witness A (witnessP9_290 i) 1800 (RealPinwheel.FiveSixths.checked_P9_290 i).1 (RealPinwheel.FiveSixths.checked_P9_290 i).2
          rw [← align_10 i]
          have he : 4940 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 46 := ⟨j.val - 4985, by omega⟩
          apply of_witness A (witnessP9_291 i) 1800 (RealPinwheel.FiveSixths.checked_P9_291 i).1 (RealPinwheel.FiveSixths.checked_P9_291 i).2
          rw [← align_11 i]
          have he : 4985 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 5077
        ·
          let i : Fin 46 := ⟨j.val - 5031, by omega⟩
          apply of_witness A (witnessP9_292 i) 1800 (RealPinwheel.FiveSixths.checked_P9_292 i).1 (RealPinwheel.FiveSixths.checked_P9_292 i).2
          rw [← align_12 i]
          have he : 5031 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 5123
          ·
            let i : Fin 46 := ⟨j.val - 5077, by omega⟩
            apply of_witness A (witnessP9_293 i) 1800 (RealPinwheel.FiveSixths.checked_P9_293 i).1 (RealPinwheel.FiveSixths.checked_P9_293 i).2
            rw [← align_13 i]
            have he : 5077 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 46 := ⟨j.val - 5123, by omega⟩
            apply of_witness A (witnessP9_294 i) 1800 (RealPinwheel.FiveSixths.checked_P9_294 i).1 (RealPinwheel.FiveSixths.checked_P9_294 i).2
            rw [← align_14 i]
            have he : 5123 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 5265
      ·
        by_cases h15_17 : j.val < 5216
        ·
          let i : Fin 47 := ⟨j.val - 5169, by omega⟩
          apply of_witness A (witnessP9_295 i) 1800 (RealPinwheel.FiveSixths.checked_P9_295 i).1 (RealPinwheel.FiveSixths.checked_P9_295 i).2
          rw [← align_15 i]
          have he : 5169 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 49 := ⟨j.val - 5216, by omega⟩
          apply of_witness A (witnessP9_296 i) 1800 (RealPinwheel.FiveSixths.checked_P9_296 i).1 (RealPinwheel.FiveSixths.checked_P9_296 i).2
          rw [← align_16 i]
          have he : 5216 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 5315
        ·
          let i : Fin 50 := ⟨j.val - 5265, by omega⟩
          apply of_witness A (witnessP9_297 i) 1800 (RealPinwheel.FiveSixths.checked_P9_297 i).1 (RealPinwheel.FiveSixths.checked_P9_297 i).2
          rw [← align_17 i]
          have he : 5265 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 5365
          ·
            let i : Fin 50 := ⟨j.val - 5315, by omega⟩
            apply of_witness A (witnessP9_298 i) 1800 (RealPinwheel.FiveSixths.checked_P9_298 i).1 (RealPinwheel.FiveSixths.checked_P9_298 i).2
            rw [← align_18 i]
            have he : 5315 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 50 := ⟨j.val - 5365, by omega⟩
            apply of_witness A (witnessP9_299 i) 1800 (RealPinwheel.FiveSixths.checked_P9_299 i).1 (RealPinwheel.FiveSixths.checked_P9_299 i).2
            rw [← align_19 i]
            have he : 5365 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
