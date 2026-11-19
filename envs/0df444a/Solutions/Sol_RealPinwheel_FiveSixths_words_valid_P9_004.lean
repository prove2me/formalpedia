-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_004
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:31:07.187007+00:00
-- url     : https://prove2.me/submissions/51e743cb-3e08-4dca-b237-bb39e6fd27b1

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_080
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_081
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_082
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_083
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_084
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_085
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_086
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_087
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_088
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_089
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_090
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_091
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_092
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_093
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_094
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_095
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_096
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_097
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_098
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_099
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
    (hlo : 362 ≤ j.val) (hhi : j.val < 532)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 8, codeFunctionP9 (362 + i.val) = (witnessP9_080 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 8, codeFunctionP9 (370 + i.val) = (witnessP9_081 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 8, codeFunctionP9 (378 + i.val) = (witnessP9_082 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 8, codeFunctionP9 (386 + i.val) = (witnessP9_083 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 8, codeFunctionP9 (394 + i.val) = (witnessP9_084 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 8, codeFunctionP9 (402 + i.val) = (witnessP9_085 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 8, codeFunctionP9 (410 + i.val) = (witnessP9_086 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 8, codeFunctionP9 (418 + i.val) = (witnessP9_087 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 8, codeFunctionP9 (426 + i.val) = (witnessP9_088 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 8, codeFunctionP9 (434 + i.val) = (witnessP9_089 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 9, codeFunctionP9 (442 + i.val) = (witnessP9_090 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 9, codeFunctionP9 (451 + i.val) = (witnessP9_091 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 9, codeFunctionP9 (460 + i.val) = (witnessP9_092 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 9, codeFunctionP9 (469 + i.val) = (witnessP9_093 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 9, codeFunctionP9 (478 + i.val) = (witnessP9_094 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 9, codeFunctionP9 (487 + i.val) = (witnessP9_095 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 9, codeFunctionP9 (496 + i.val) = (witnessP9_096 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 9, codeFunctionP9 (505 + i.val) = (witnessP9_097 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 9, codeFunctionP9 (514 + i.val) = (witnessP9_098 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 9, codeFunctionP9 (523 + i.val) = (witnessP9_099 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 442
  ·
    by_cases h0_10 : j.val < 402
    ·
      by_cases h0_5 : j.val < 378
      ·
        by_cases h0_2 : j.val < 370
        ·
          let i : Fin 8 := ⟨j.val - 362, by omega⟩
          apply of_witness A (witnessP9_080 i) 1800 (RealPinwheel.FiveSixths.checked_P9_080 i).1 (RealPinwheel.FiveSixths.checked_P9_080 i).2
          rw [← align_0 i]
          have he : 362 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 8 := ⟨j.val - 370, by omega⟩
          apply of_witness A (witnessP9_081 i) 1800 (RealPinwheel.FiveSixths.checked_P9_081 i).1 (RealPinwheel.FiveSixths.checked_P9_081 i).2
          rw [← align_1 i]
          have he : 370 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 386
        ·
          let i : Fin 8 := ⟨j.val - 378, by omega⟩
          apply of_witness A (witnessP9_082 i) 1800 (RealPinwheel.FiveSixths.checked_P9_082 i).1 (RealPinwheel.FiveSixths.checked_P9_082 i).2
          rw [← align_2 i]
          have he : 378 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 394
          ·
            let i : Fin 8 := ⟨j.val - 386, by omega⟩
            apply of_witness A (witnessP9_083 i) 1800 (RealPinwheel.FiveSixths.checked_P9_083 i).1 (RealPinwheel.FiveSixths.checked_P9_083 i).2
            rw [← align_3 i]
            have he : 386 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 8 := ⟨j.val - 394, by omega⟩
            apply of_witness A (witnessP9_084 i) 1800 (RealPinwheel.FiveSixths.checked_P9_084 i).1 (RealPinwheel.FiveSixths.checked_P9_084 i).2
            rw [← align_4 i]
            have he : 394 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 418
      ·
        by_cases h5_7 : j.val < 410
        ·
          let i : Fin 8 := ⟨j.val - 402, by omega⟩
          apply of_witness A (witnessP9_085 i) 1800 (RealPinwheel.FiveSixths.checked_P9_085 i).1 (RealPinwheel.FiveSixths.checked_P9_085 i).2
          rw [← align_5 i]
          have he : 402 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 8 := ⟨j.val - 410, by omega⟩
          apply of_witness A (witnessP9_086 i) 1800 (RealPinwheel.FiveSixths.checked_P9_086 i).1 (RealPinwheel.FiveSixths.checked_P9_086 i).2
          rw [← align_6 i]
          have he : 410 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 426
        ·
          let i : Fin 8 := ⟨j.val - 418, by omega⟩
          apply of_witness A (witnessP9_087 i) 1800 (RealPinwheel.FiveSixths.checked_P9_087 i).1 (RealPinwheel.FiveSixths.checked_P9_087 i).2
          rw [← align_7 i]
          have he : 418 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 434
          ·
            let i : Fin 8 := ⟨j.val - 426, by omega⟩
            apply of_witness A (witnessP9_088 i) 1800 (RealPinwheel.FiveSixths.checked_P9_088 i).1 (RealPinwheel.FiveSixths.checked_P9_088 i).2
            rw [← align_8 i]
            have he : 426 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 8 := ⟨j.val - 434, by omega⟩
            apply of_witness A (witnessP9_089 i) 1800 (RealPinwheel.FiveSixths.checked_P9_089 i).1 (RealPinwheel.FiveSixths.checked_P9_089 i).2
            rw [← align_9 i]
            have he : 434 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 487
    ·
      by_cases h10_15 : j.val < 460
      ·
        by_cases h10_12 : j.val < 451
        ·
          let i : Fin 9 := ⟨j.val - 442, by omega⟩
          apply of_witness A (witnessP9_090 i) 1800 (RealPinwheel.FiveSixths.checked_P9_090 i).1 (RealPinwheel.FiveSixths.checked_P9_090 i).2
          rw [← align_10 i]
          have he : 442 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 9 := ⟨j.val - 451, by omega⟩
          apply of_witness A (witnessP9_091 i) 1800 (RealPinwheel.FiveSixths.checked_P9_091 i).1 (RealPinwheel.FiveSixths.checked_P9_091 i).2
          rw [← align_11 i]
          have he : 451 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 469
        ·
          let i : Fin 9 := ⟨j.val - 460, by omega⟩
          apply of_witness A (witnessP9_092 i) 1800 (RealPinwheel.FiveSixths.checked_P9_092 i).1 (RealPinwheel.FiveSixths.checked_P9_092 i).2
          rw [← align_12 i]
          have he : 460 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 478
          ·
            let i : Fin 9 := ⟨j.val - 469, by omega⟩
            apply of_witness A (witnessP9_093 i) 1800 (RealPinwheel.FiveSixths.checked_P9_093 i).1 (RealPinwheel.FiveSixths.checked_P9_093 i).2
            rw [← align_13 i]
            have he : 469 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 9 := ⟨j.val - 478, by omega⟩
            apply of_witness A (witnessP9_094 i) 1800 (RealPinwheel.FiveSixths.checked_P9_094 i).1 (RealPinwheel.FiveSixths.checked_P9_094 i).2
            rw [← align_14 i]
            have he : 478 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 505
      ·
        by_cases h15_17 : j.val < 496
        ·
          let i : Fin 9 := ⟨j.val - 487, by omega⟩
          apply of_witness A (witnessP9_095 i) 1800 (RealPinwheel.FiveSixths.checked_P9_095 i).1 (RealPinwheel.FiveSixths.checked_P9_095 i).2
          rw [← align_15 i]
          have he : 487 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 9 := ⟨j.val - 496, by omega⟩
          apply of_witness A (witnessP9_096 i) 1800 (RealPinwheel.FiveSixths.checked_P9_096 i).1 (RealPinwheel.FiveSixths.checked_P9_096 i).2
          rw [← align_16 i]
          have he : 496 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 514
        ·
          let i : Fin 9 := ⟨j.val - 505, by omega⟩
          apply of_witness A (witnessP9_097 i) 1800 (RealPinwheel.FiveSixths.checked_P9_097 i).1 (RealPinwheel.FiveSixths.checked_P9_097 i).2
          rw [← align_17 i]
          have he : 505 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 523
          ·
            let i : Fin 9 := ⟨j.val - 514, by omega⟩
            apply of_witness A (witnessP9_098 i) 1800 (RealPinwheel.FiveSixths.checked_P9_098 i).1 (RealPinwheel.FiveSixths.checked_P9_098 i).2
            rw [← align_18 i]
            have he : 514 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 9 := ⟨j.val - 523, by omega⟩
            apply of_witness A (witnessP9_099 i) 1800 (RealPinwheel.FiveSixths.checked_P9_099 i).1 (RealPinwheel.FiveSixths.checked_P9_099 i).2
            rw [← align_19 i]
            have he : 523 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
