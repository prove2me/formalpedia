-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_small_005
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:49:45.572364+00:00
-- url     : https://prove2.me/submissions/971001a0-5b7a-4b81-af87-068ab4f0b273

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_100
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_101
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_102
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_103
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_104
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_105
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_106
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_107
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_108
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_109
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_110
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_111
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_112
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_113
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_114
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_115
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_116
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_117
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_118
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_119
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
    (hlo : 660 ≤ j.val) (hhi : j.val < 890)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 11, codeFunctionD8 (660 + i.val) = (witnessD8_100 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 11, codeFunctionD8 (671 + i.val) = (witnessD8_101 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 11, codeFunctionD8 (682 + i.val) = (witnessD8_102 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 11, codeFunctionD8 (693 + i.val) = (witnessD8_103 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 11, codeFunctionD8 (704 + i.val) = (witnessD8_104 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 11, codeFunctionD8 (715 + i.val) = (witnessD8_105 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 11, codeFunctionD8 (726 + i.val) = (witnessD8_106 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 11, codeFunctionD8 (737 + i.val) = (witnessD8_107 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 11, codeFunctionD8 (748 + i.val) = (witnessD8_108 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 11, codeFunctionD8 (759 + i.val) = (witnessD8_109 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 12, codeFunctionD8 (770 + i.val) = (witnessD8_110 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 12, codeFunctionD8 (782 + i.val) = (witnessD8_111 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 12, codeFunctionD8 (794 + i.val) = (witnessD8_112 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 12, codeFunctionD8 (806 + i.val) = (witnessD8_113 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 12, codeFunctionD8 (818 + i.val) = (witnessD8_114 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 12, codeFunctionD8 (830 + i.val) = (witnessD8_115 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 12, codeFunctionD8 (842 + i.val) = (witnessD8_116 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 12, codeFunctionD8 (854 + i.val) = (witnessD8_117 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 12, codeFunctionD8 (866 + i.val) = (witnessD8_118 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 12, codeFunctionD8 (878 + i.val) = (witnessD8_119 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 770
  ·
    by_cases h0_10 : j.val < 715
    ·
      by_cases h0_5 : j.val < 682
      ·
        by_cases h0_2 : j.val < 671
        ·
          let i : Fin 11 := ⟨j.val - 660, by omega⟩
          apply of_witness A (witnessD8_100 i) 608 (RealPinwheel.FiveSixths.checked_D8_100 i).1 (RealPinwheel.FiveSixths.checked_D8_100 i).2
          rw [← align_0 i]
          have he : 660 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 11 := ⟨j.val - 671, by omega⟩
          apply of_witness A (witnessD8_101 i) 608 (RealPinwheel.FiveSixths.checked_D8_101 i).1 (RealPinwheel.FiveSixths.checked_D8_101 i).2
          rw [← align_1 i]
          have he : 671 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 693
        ·
          let i : Fin 11 := ⟨j.val - 682, by omega⟩
          apply of_witness A (witnessD8_102 i) 608 (RealPinwheel.FiveSixths.checked_D8_102 i).1 (RealPinwheel.FiveSixths.checked_D8_102 i).2
          rw [← align_2 i]
          have he : 682 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 704
          ·
            let i : Fin 11 := ⟨j.val - 693, by omega⟩
            apply of_witness A (witnessD8_103 i) 608 (RealPinwheel.FiveSixths.checked_D8_103 i).1 (RealPinwheel.FiveSixths.checked_D8_103 i).2
            rw [← align_3 i]
            have he : 693 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 11 := ⟨j.val - 704, by omega⟩
            apply of_witness A (witnessD8_104 i) 608 (RealPinwheel.FiveSixths.checked_D8_104 i).1 (RealPinwheel.FiveSixths.checked_D8_104 i).2
            rw [← align_4 i]
            have he : 704 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 737
      ·
        by_cases h5_7 : j.val < 726
        ·
          let i : Fin 11 := ⟨j.val - 715, by omega⟩
          apply of_witness A (witnessD8_105 i) 608 (RealPinwheel.FiveSixths.checked_D8_105 i).1 (RealPinwheel.FiveSixths.checked_D8_105 i).2
          rw [← align_5 i]
          have he : 715 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 11 := ⟨j.val - 726, by omega⟩
          apply of_witness A (witnessD8_106 i) 608 (RealPinwheel.FiveSixths.checked_D8_106 i).1 (RealPinwheel.FiveSixths.checked_D8_106 i).2
          rw [← align_6 i]
          have he : 726 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 748
        ·
          let i : Fin 11 := ⟨j.val - 737, by omega⟩
          apply of_witness A (witnessD8_107 i) 608 (RealPinwheel.FiveSixths.checked_D8_107 i).1 (RealPinwheel.FiveSixths.checked_D8_107 i).2
          rw [← align_7 i]
          have he : 737 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 759
          ·
            let i : Fin 11 := ⟨j.val - 748, by omega⟩
            apply of_witness A (witnessD8_108 i) 608 (RealPinwheel.FiveSixths.checked_D8_108 i).1 (RealPinwheel.FiveSixths.checked_D8_108 i).2
            rw [← align_8 i]
            have he : 748 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 11 := ⟨j.val - 759, by omega⟩
            apply of_witness A (witnessD8_109 i) 608 (RealPinwheel.FiveSixths.checked_D8_109 i).1 (RealPinwheel.FiveSixths.checked_D8_109 i).2
            rw [← align_9 i]
            have he : 759 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 830
    ·
      by_cases h10_15 : j.val < 794
      ·
        by_cases h10_12 : j.val < 782
        ·
          let i : Fin 12 := ⟨j.val - 770, by omega⟩
          apply of_witness A (witnessD8_110 i) 608 (RealPinwheel.FiveSixths.checked_D8_110 i).1 (RealPinwheel.FiveSixths.checked_D8_110 i).2
          rw [← align_10 i]
          have he : 770 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 12 := ⟨j.val - 782, by omega⟩
          apply of_witness A (witnessD8_111 i) 608 (RealPinwheel.FiveSixths.checked_D8_111 i).1 (RealPinwheel.FiveSixths.checked_D8_111 i).2
          rw [← align_11 i]
          have he : 782 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 806
        ·
          let i : Fin 12 := ⟨j.val - 794, by omega⟩
          apply of_witness A (witnessD8_112 i) 608 (RealPinwheel.FiveSixths.checked_D8_112 i).1 (RealPinwheel.FiveSixths.checked_D8_112 i).2
          rw [← align_12 i]
          have he : 794 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 818
          ·
            let i : Fin 12 := ⟨j.val - 806, by omega⟩
            apply of_witness A (witnessD8_113 i) 608 (RealPinwheel.FiveSixths.checked_D8_113 i).1 (RealPinwheel.FiveSixths.checked_D8_113 i).2
            rw [← align_13 i]
            have he : 806 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 12 := ⟨j.val - 818, by omega⟩
            apply of_witness A (witnessD8_114 i) 608 (RealPinwheel.FiveSixths.checked_D8_114 i).1 (RealPinwheel.FiveSixths.checked_D8_114 i).2
            rw [← align_14 i]
            have he : 818 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 854
      ·
        by_cases h15_17 : j.val < 842
        ·
          let i : Fin 12 := ⟨j.val - 830, by omega⟩
          apply of_witness A (witnessD8_115 i) 608 (RealPinwheel.FiveSixths.checked_D8_115 i).1 (RealPinwheel.FiveSixths.checked_D8_115 i).2
          rw [← align_15 i]
          have he : 830 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 12 := ⟨j.val - 842, by omega⟩
          apply of_witness A (witnessD8_116 i) 608 (RealPinwheel.FiveSixths.checked_D8_116 i).1 (RealPinwheel.FiveSixths.checked_D8_116 i).2
          rw [← align_16 i]
          have he : 842 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 866
        ·
          let i : Fin 12 := ⟨j.val - 854, by omega⟩
          apply of_witness A (witnessD8_117 i) 608 (RealPinwheel.FiveSixths.checked_D8_117 i).1 (RealPinwheel.FiveSixths.checked_D8_117 i).2
          rw [← align_17 i]
          have he : 854 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 878
          ·
            let i : Fin 12 := ⟨j.val - 866, by omega⟩
            apply of_witness A (witnessD8_118 i) 608 (RealPinwheel.FiveSixths.checked_D8_118 i).1 (RealPinwheel.FiveSixths.checked_D8_118 i).2
            rw [← align_18 i]
            have he : 866 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 12 := ⟨j.val - 878, by omega⟩
            apply of_witness A (witnessD8_119 i) 608 (RealPinwheel.FiveSixths.checked_D8_119 i).1 (RealPinwheel.FiveSixths.checked_D8_119 i).2
            rw [← align_19 i]
            have he : 878 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
