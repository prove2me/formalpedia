-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_005
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:02:47.487614+00:00
-- url     : https://prove2.me/submissions/7399568f-f36f-4042-b9f6-6858d3c0f1c4

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_100
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_101
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_102
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_103
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_104
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_105
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_106
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_107
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_108
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_109
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_110
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_111
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_112
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_113
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_114
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_115
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_116
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_117
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_118
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_119
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
    (hlo : 532 ≤ j.val) (hhi : j.val < 746)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 10, codeFunctionP9 (532 + i.val) = (witnessP9_100 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 10, codeFunctionP9 (542 + i.val) = (witnessP9_101 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 10, codeFunctionP9 (552 + i.val) = (witnessP9_102 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 10, codeFunctionP9 (562 + i.val) = (witnessP9_103 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 10, codeFunctionP9 (572 + i.val) = (witnessP9_104 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 10, codeFunctionP9 (582 + i.val) = (witnessP9_105 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 10, codeFunctionP9 (592 + i.val) = (witnessP9_106 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 10, codeFunctionP9 (602 + i.val) = (witnessP9_107 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 11, codeFunctionP9 (612 + i.val) = (witnessP9_108 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 11, codeFunctionP9 (623 + i.val) = (witnessP9_109 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 11, codeFunctionP9 (634 + i.val) = (witnessP9_110 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 11, codeFunctionP9 (645 + i.val) = (witnessP9_111 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 11, codeFunctionP9 (656 + i.val) = (witnessP9_112 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 11, codeFunctionP9 (667 + i.val) = (witnessP9_113 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 11, codeFunctionP9 (678 + i.val) = (witnessP9_114 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 11, codeFunctionP9 (689 + i.val) = (witnessP9_115 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 11, codeFunctionP9 (700 + i.val) = (witnessP9_116 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 11, codeFunctionP9 (711 + i.val) = (witnessP9_117 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 12, codeFunctionP9 (722 + i.val) = (witnessP9_118 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 12, codeFunctionP9 (734 + i.val) = (witnessP9_119 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 634
  ·
    by_cases h0_10 : j.val < 582
    ·
      by_cases h0_5 : j.val < 552
      ·
        by_cases h0_2 : j.val < 542
        ·
          let i : Fin 10 := ⟨j.val - 532, by omega⟩
          apply of_witness A (witnessP9_100 i) 1800 (RealPinwheel.FiveSixths.checked_P9_100 i).1 (RealPinwheel.FiveSixths.checked_P9_100 i).2
          rw [← align_0 i]
          have he : 532 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 10 := ⟨j.val - 542, by omega⟩
          apply of_witness A (witnessP9_101 i) 1800 (RealPinwheel.FiveSixths.checked_P9_101 i).1 (RealPinwheel.FiveSixths.checked_P9_101 i).2
          rw [← align_1 i]
          have he : 542 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 562
        ·
          let i : Fin 10 := ⟨j.val - 552, by omega⟩
          apply of_witness A (witnessP9_102 i) 1800 (RealPinwheel.FiveSixths.checked_P9_102 i).1 (RealPinwheel.FiveSixths.checked_P9_102 i).2
          rw [← align_2 i]
          have he : 552 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 572
          ·
            let i : Fin 10 := ⟨j.val - 562, by omega⟩
            apply of_witness A (witnessP9_103 i) 1800 (RealPinwheel.FiveSixths.checked_P9_103 i).1 (RealPinwheel.FiveSixths.checked_P9_103 i).2
            rw [← align_3 i]
            have he : 562 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 10 := ⟨j.val - 572, by omega⟩
            apply of_witness A (witnessP9_104 i) 1800 (RealPinwheel.FiveSixths.checked_P9_104 i).1 (RealPinwheel.FiveSixths.checked_P9_104 i).2
            rw [← align_4 i]
            have he : 572 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 602
      ·
        by_cases h5_7 : j.val < 592
        ·
          let i : Fin 10 := ⟨j.val - 582, by omega⟩
          apply of_witness A (witnessP9_105 i) 1800 (RealPinwheel.FiveSixths.checked_P9_105 i).1 (RealPinwheel.FiveSixths.checked_P9_105 i).2
          rw [← align_5 i]
          have he : 582 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 10 := ⟨j.val - 592, by omega⟩
          apply of_witness A (witnessP9_106 i) 1800 (RealPinwheel.FiveSixths.checked_P9_106 i).1 (RealPinwheel.FiveSixths.checked_P9_106 i).2
          rw [← align_6 i]
          have he : 592 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 612
        ·
          let i : Fin 10 := ⟨j.val - 602, by omega⟩
          apply of_witness A (witnessP9_107 i) 1800 (RealPinwheel.FiveSixths.checked_P9_107 i).1 (RealPinwheel.FiveSixths.checked_P9_107 i).2
          rw [← align_7 i]
          have he : 602 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 623
          ·
            let i : Fin 11 := ⟨j.val - 612, by omega⟩
            apply of_witness A (witnessP9_108 i) 1800 (RealPinwheel.FiveSixths.checked_P9_108 i).1 (RealPinwheel.FiveSixths.checked_P9_108 i).2
            rw [← align_8 i]
            have he : 612 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 11 := ⟨j.val - 623, by omega⟩
            apply of_witness A (witnessP9_109 i) 1800 (RealPinwheel.FiveSixths.checked_P9_109 i).1 (RealPinwheel.FiveSixths.checked_P9_109 i).2
            rw [← align_9 i]
            have he : 623 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 689
    ·
      by_cases h10_15 : j.val < 656
      ·
        by_cases h10_12 : j.val < 645
        ·
          let i : Fin 11 := ⟨j.val - 634, by omega⟩
          apply of_witness A (witnessP9_110 i) 1800 (RealPinwheel.FiveSixths.checked_P9_110 i).1 (RealPinwheel.FiveSixths.checked_P9_110 i).2
          rw [← align_10 i]
          have he : 634 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 11 := ⟨j.val - 645, by omega⟩
          apply of_witness A (witnessP9_111 i) 1800 (RealPinwheel.FiveSixths.checked_P9_111 i).1 (RealPinwheel.FiveSixths.checked_P9_111 i).2
          rw [← align_11 i]
          have he : 645 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 667
        ·
          let i : Fin 11 := ⟨j.val - 656, by omega⟩
          apply of_witness A (witnessP9_112 i) 1800 (RealPinwheel.FiveSixths.checked_P9_112 i).1 (RealPinwheel.FiveSixths.checked_P9_112 i).2
          rw [← align_12 i]
          have he : 656 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 678
          ·
            let i : Fin 11 := ⟨j.val - 667, by omega⟩
            apply of_witness A (witnessP9_113 i) 1800 (RealPinwheel.FiveSixths.checked_P9_113 i).1 (RealPinwheel.FiveSixths.checked_P9_113 i).2
            rw [← align_13 i]
            have he : 667 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 11 := ⟨j.val - 678, by omega⟩
            apply of_witness A (witnessP9_114 i) 1800 (RealPinwheel.FiveSixths.checked_P9_114 i).1 (RealPinwheel.FiveSixths.checked_P9_114 i).2
            rw [← align_14 i]
            have he : 678 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 711
      ·
        by_cases h15_17 : j.val < 700
        ·
          let i : Fin 11 := ⟨j.val - 689, by omega⟩
          apply of_witness A (witnessP9_115 i) 1800 (RealPinwheel.FiveSixths.checked_P9_115 i).1 (RealPinwheel.FiveSixths.checked_P9_115 i).2
          rw [← align_15 i]
          have he : 689 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 11 := ⟨j.val - 700, by omega⟩
          apply of_witness A (witnessP9_116 i) 1800 (RealPinwheel.FiveSixths.checked_P9_116 i).1 (RealPinwheel.FiveSixths.checked_P9_116 i).2
          rw [← align_16 i]
          have he : 700 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 722
        ·
          let i : Fin 11 := ⟨j.val - 711, by omega⟩
          apply of_witness A (witnessP9_117 i) 1800 (RealPinwheel.FiveSixths.checked_P9_117 i).1 (RealPinwheel.FiveSixths.checked_P9_117 i).2
          rw [← align_17 i]
          have he : 711 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 734
          ·
            let i : Fin 12 := ⟨j.val - 722, by omega⟩
            apply of_witness A (witnessP9_118 i) 1800 (RealPinwheel.FiveSixths.checked_P9_118 i).1 (RealPinwheel.FiveSixths.checked_P9_118 i).2
            rw [← align_18 i]
            have he : 722 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 12 := ⟨j.val - 734, by omega⟩
            apply of_witness A (witnessP9_119 i) 1800 (RealPinwheel.FiveSixths.checked_P9_119 i).1 (RealPinwheel.FiveSixths.checked_P9_119 i).2
            rw [← align_19 i]
            have he : 734 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
