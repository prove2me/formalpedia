-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_small_004
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:41:51.782109+00:00
-- url     : https://prove2.me/submissions/a9d464e9-08d8-425e-a567-117658775b2d

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_080
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_081
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_082
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_083
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_084
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_085
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_086
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_087
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_088
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_089
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_090
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_091
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_092
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_093
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_094
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_095
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_096
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_097
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_098
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_099
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
    (hlo : 458 ≤ j.val) (hhi : j.val < 660)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 9, codeFunctionD8 (458 + i.val) = (witnessD8_080 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 9, codeFunctionD8 (467 + i.val) = (witnessD8_081 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 10, codeFunctionD8 (476 + i.val) = (witnessD8_082 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 10, codeFunctionD8 (486 + i.val) = (witnessD8_083 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 10, codeFunctionD8 (496 + i.val) = (witnessD8_084 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 10, codeFunctionD8 (506 + i.val) = (witnessD8_085 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 10, codeFunctionD8 (516 + i.val) = (witnessD8_086 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 10, codeFunctionD8 (526 + i.val) = (witnessD8_087 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 10, codeFunctionD8 (536 + i.val) = (witnessD8_088 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 10, codeFunctionD8 (546 + i.val) = (witnessD8_089 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 10, codeFunctionD8 (556 + i.val) = (witnessD8_090 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 10, codeFunctionD8 (566 + i.val) = (witnessD8_091 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 10, codeFunctionD8 (576 + i.val) = (witnessD8_092 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 10, codeFunctionD8 (586 + i.val) = (witnessD8_093 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 10, codeFunctionD8 (596 + i.val) = (witnessD8_094 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 10, codeFunctionD8 (606 + i.val) = (witnessD8_095 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 11, codeFunctionD8 (616 + i.val) = (witnessD8_096 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 11, codeFunctionD8 (627 + i.val) = (witnessD8_097 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 11, codeFunctionD8 (638 + i.val) = (witnessD8_098 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 11, codeFunctionD8 (649 + i.val) = (witnessD8_099 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 556
  ·
    by_cases h0_10 : j.val < 506
    ·
      by_cases h0_5 : j.val < 476
      ·
        by_cases h0_2 : j.val < 467
        ·
          let i : Fin 9 := ⟨j.val - 458, by omega⟩
          apply of_witness A (witnessD8_080 i) 608 (RealPinwheel.FiveSixths.checked_D8_080 i).1 (RealPinwheel.FiveSixths.checked_D8_080 i).2
          rw [← align_0 i]
          have he : 458 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 9 := ⟨j.val - 467, by omega⟩
          apply of_witness A (witnessD8_081 i) 608 (RealPinwheel.FiveSixths.checked_D8_081 i).1 (RealPinwheel.FiveSixths.checked_D8_081 i).2
          rw [← align_1 i]
          have he : 467 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 486
        ·
          let i : Fin 10 := ⟨j.val - 476, by omega⟩
          apply of_witness A (witnessD8_082 i) 608 (RealPinwheel.FiveSixths.checked_D8_082 i).1 (RealPinwheel.FiveSixths.checked_D8_082 i).2
          rw [← align_2 i]
          have he : 476 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 496
          ·
            let i : Fin 10 := ⟨j.val - 486, by omega⟩
            apply of_witness A (witnessD8_083 i) 608 (RealPinwheel.FiveSixths.checked_D8_083 i).1 (RealPinwheel.FiveSixths.checked_D8_083 i).2
            rw [← align_3 i]
            have he : 486 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 10 := ⟨j.val - 496, by omega⟩
            apply of_witness A (witnessD8_084 i) 608 (RealPinwheel.FiveSixths.checked_D8_084 i).1 (RealPinwheel.FiveSixths.checked_D8_084 i).2
            rw [← align_4 i]
            have he : 496 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 526
      ·
        by_cases h5_7 : j.val < 516
        ·
          let i : Fin 10 := ⟨j.val - 506, by omega⟩
          apply of_witness A (witnessD8_085 i) 608 (RealPinwheel.FiveSixths.checked_D8_085 i).1 (RealPinwheel.FiveSixths.checked_D8_085 i).2
          rw [← align_5 i]
          have he : 506 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 10 := ⟨j.val - 516, by omega⟩
          apply of_witness A (witnessD8_086 i) 608 (RealPinwheel.FiveSixths.checked_D8_086 i).1 (RealPinwheel.FiveSixths.checked_D8_086 i).2
          rw [← align_6 i]
          have he : 516 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 536
        ·
          let i : Fin 10 := ⟨j.val - 526, by omega⟩
          apply of_witness A (witnessD8_087 i) 608 (RealPinwheel.FiveSixths.checked_D8_087 i).1 (RealPinwheel.FiveSixths.checked_D8_087 i).2
          rw [← align_7 i]
          have he : 526 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 546
          ·
            let i : Fin 10 := ⟨j.val - 536, by omega⟩
            apply of_witness A (witnessD8_088 i) 608 (RealPinwheel.FiveSixths.checked_D8_088 i).1 (RealPinwheel.FiveSixths.checked_D8_088 i).2
            rw [← align_8 i]
            have he : 536 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 10 := ⟨j.val - 546, by omega⟩
            apply of_witness A (witnessD8_089 i) 608 (RealPinwheel.FiveSixths.checked_D8_089 i).1 (RealPinwheel.FiveSixths.checked_D8_089 i).2
            rw [← align_9 i]
            have he : 546 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 606
    ·
      by_cases h10_15 : j.val < 576
      ·
        by_cases h10_12 : j.val < 566
        ·
          let i : Fin 10 := ⟨j.val - 556, by omega⟩
          apply of_witness A (witnessD8_090 i) 608 (RealPinwheel.FiveSixths.checked_D8_090 i).1 (RealPinwheel.FiveSixths.checked_D8_090 i).2
          rw [← align_10 i]
          have he : 556 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 10 := ⟨j.val - 566, by omega⟩
          apply of_witness A (witnessD8_091 i) 608 (RealPinwheel.FiveSixths.checked_D8_091 i).1 (RealPinwheel.FiveSixths.checked_D8_091 i).2
          rw [← align_11 i]
          have he : 566 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 586
        ·
          let i : Fin 10 := ⟨j.val - 576, by omega⟩
          apply of_witness A (witnessD8_092 i) 608 (RealPinwheel.FiveSixths.checked_D8_092 i).1 (RealPinwheel.FiveSixths.checked_D8_092 i).2
          rw [← align_12 i]
          have he : 576 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 596
          ·
            let i : Fin 10 := ⟨j.val - 586, by omega⟩
            apply of_witness A (witnessD8_093 i) 608 (RealPinwheel.FiveSixths.checked_D8_093 i).1 (RealPinwheel.FiveSixths.checked_D8_093 i).2
            rw [← align_13 i]
            have he : 586 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 10 := ⟨j.val - 596, by omega⟩
            apply of_witness A (witnessD8_094 i) 608 (RealPinwheel.FiveSixths.checked_D8_094 i).1 (RealPinwheel.FiveSixths.checked_D8_094 i).2
            rw [← align_14 i]
            have he : 596 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 627
      ·
        by_cases h15_17 : j.val < 616
        ·
          let i : Fin 10 := ⟨j.val - 606, by omega⟩
          apply of_witness A (witnessD8_095 i) 608 (RealPinwheel.FiveSixths.checked_D8_095 i).1 (RealPinwheel.FiveSixths.checked_D8_095 i).2
          rw [← align_15 i]
          have he : 606 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 11 := ⟨j.val - 616, by omega⟩
          apply of_witness A (witnessD8_096 i) 608 (RealPinwheel.FiveSixths.checked_D8_096 i).1 (RealPinwheel.FiveSixths.checked_D8_096 i).2
          rw [← align_16 i]
          have he : 616 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 638
        ·
          let i : Fin 11 := ⟨j.val - 627, by omega⟩
          apply of_witness A (witnessD8_097 i) 608 (RealPinwheel.FiveSixths.checked_D8_097 i).1 (RealPinwheel.FiveSixths.checked_D8_097 i).2
          rw [← align_17 i]
          have he : 627 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 649
          ·
            let i : Fin 11 := ⟨j.val - 638, by omega⟩
            apply of_witness A (witnessD8_098 i) 608 (RealPinwheel.FiveSixths.checked_D8_098 i).1 (RealPinwheel.FiveSixths.checked_D8_098 i).2
            rw [← align_18 i]
            have he : 638 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 11 := ⟨j.val - 649, by omega⟩
            apply of_witness A (witnessD8_099 i) 608 (RealPinwheel.FiveSixths.checked_D8_099 i).1 (RealPinwheel.FiveSixths.checked_D8_099 i).2
            rw [← align_19 i]
            have he : 649 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
