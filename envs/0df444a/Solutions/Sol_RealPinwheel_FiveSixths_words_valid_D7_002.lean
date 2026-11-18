-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D7_002
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:08:04.742147+00:00
-- url     : https://prove2.me/submissions/98e50a7c-a8cc-41f6-a909-828c8eee5014

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD7
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_040
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_041
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_042
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_043
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_044
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_045
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_046
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_047
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_048
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_049
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_050
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_051
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_052
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_053
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_054
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_055
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_056
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_057
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_058
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_059
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

theorem solution (A : Instance 7) (j : Fin 1657)
    (hlo : 558 ≤ j.val) (hhi : j.val < 1095)
    (hb : codeBox (codeFunctionD7 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 7), 0 < L ∧ L ≤ 352 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 22, codeFunctionD7 (558 + i.val) = (witnessD7_040 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 23, codeFunctionD7 (580 + i.val) = (witnessD7_041 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 23, codeFunctionD7 (603 + i.val) = (witnessD7_042 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 23, codeFunctionD7 (626 + i.val) = (witnessD7_043 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 25, codeFunctionD7 (649 + i.val) = (witnessD7_044 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 25, codeFunctionD7 (674 + i.val) = (witnessD7_045 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 25, codeFunctionD7 (699 + i.val) = (witnessD7_046 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 26, codeFunctionD7 (724 + i.val) = (witnessD7_047 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 26, codeFunctionD7 (750 + i.val) = (witnessD7_048 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 27, codeFunctionD7 (776 + i.val) = (witnessD7_049 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 27, codeFunctionD7 (803 + i.val) = (witnessD7_050 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 27, codeFunctionD7 (830 + i.val) = (witnessD7_051 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 27, codeFunctionD7 (857 + i.val) = (witnessD7_052 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 29, codeFunctionD7 (884 + i.val) = (witnessD7_053 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 29, codeFunctionD7 (913 + i.val) = (witnessD7_054 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 29, codeFunctionD7 (942 + i.val) = (witnessD7_055 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 30, codeFunctionD7 (971 + i.val) = (witnessD7_056 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 31, codeFunctionD7 (1001 + i.val) = (witnessD7_057 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 31, codeFunctionD7 (1032 + i.val) = (witnessD7_058 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 32, codeFunctionD7 (1063 + i.val) = (witnessD7_059 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 803
  ·
    by_cases h0_10 : j.val < 674
    ·
      by_cases h0_5 : j.val < 603
      ·
        by_cases h0_2 : j.val < 580
        ·
          let i : Fin 22 := ⟨j.val - 558, by omega⟩
          apply of_witness A (witnessD7_040 i) 352 (RealPinwheel.FiveSixths.checked_D7_040 i).1 (RealPinwheel.FiveSixths.checked_D7_040 i).2
          rw [← align_0 i]
          have he : 558 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 23 := ⟨j.val - 580, by omega⟩
          apply of_witness A (witnessD7_041 i) 352 (RealPinwheel.FiveSixths.checked_D7_041 i).1 (RealPinwheel.FiveSixths.checked_D7_041 i).2
          rw [← align_1 i]
          have he : 580 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 626
        ·
          let i : Fin 23 := ⟨j.val - 603, by omega⟩
          apply of_witness A (witnessD7_042 i) 352 (RealPinwheel.FiveSixths.checked_D7_042 i).1 (RealPinwheel.FiveSixths.checked_D7_042 i).2
          rw [← align_2 i]
          have he : 603 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 649
          ·
            let i : Fin 23 := ⟨j.val - 626, by omega⟩
            apply of_witness A (witnessD7_043 i) 352 (RealPinwheel.FiveSixths.checked_D7_043 i).1 (RealPinwheel.FiveSixths.checked_D7_043 i).2
            rw [← align_3 i]
            have he : 626 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 25 := ⟨j.val - 649, by omega⟩
            apply of_witness A (witnessD7_044 i) 352 (RealPinwheel.FiveSixths.checked_D7_044 i).1 (RealPinwheel.FiveSixths.checked_D7_044 i).2
            rw [← align_4 i]
            have he : 649 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 724
      ·
        by_cases h5_7 : j.val < 699
        ·
          let i : Fin 25 := ⟨j.val - 674, by omega⟩
          apply of_witness A (witnessD7_045 i) 352 (RealPinwheel.FiveSixths.checked_D7_045 i).1 (RealPinwheel.FiveSixths.checked_D7_045 i).2
          rw [← align_5 i]
          have he : 674 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 25 := ⟨j.val - 699, by omega⟩
          apply of_witness A (witnessD7_046 i) 352 (RealPinwheel.FiveSixths.checked_D7_046 i).1 (RealPinwheel.FiveSixths.checked_D7_046 i).2
          rw [← align_6 i]
          have he : 699 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 750
        ·
          let i : Fin 26 := ⟨j.val - 724, by omega⟩
          apply of_witness A (witnessD7_047 i) 352 (RealPinwheel.FiveSixths.checked_D7_047 i).1 (RealPinwheel.FiveSixths.checked_D7_047 i).2
          rw [← align_7 i]
          have he : 724 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 776
          ·
            let i : Fin 26 := ⟨j.val - 750, by omega⟩
            apply of_witness A (witnessD7_048 i) 352 (RealPinwheel.FiveSixths.checked_D7_048 i).1 (RealPinwheel.FiveSixths.checked_D7_048 i).2
            rw [← align_8 i]
            have he : 750 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 27 := ⟨j.val - 776, by omega⟩
            apply of_witness A (witnessD7_049 i) 352 (RealPinwheel.FiveSixths.checked_D7_049 i).1 (RealPinwheel.FiveSixths.checked_D7_049 i).2
            rw [← align_9 i]
            have he : 776 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 942
    ·
      by_cases h10_15 : j.val < 857
      ·
        by_cases h10_12 : j.val < 830
        ·
          let i : Fin 27 := ⟨j.val - 803, by omega⟩
          apply of_witness A (witnessD7_050 i) 352 (RealPinwheel.FiveSixths.checked_D7_050 i).1 (RealPinwheel.FiveSixths.checked_D7_050 i).2
          rw [← align_10 i]
          have he : 803 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 27 := ⟨j.val - 830, by omega⟩
          apply of_witness A (witnessD7_051 i) 352 (RealPinwheel.FiveSixths.checked_D7_051 i).1 (RealPinwheel.FiveSixths.checked_D7_051 i).2
          rw [← align_11 i]
          have he : 830 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 884
        ·
          let i : Fin 27 := ⟨j.val - 857, by omega⟩
          apply of_witness A (witnessD7_052 i) 352 (RealPinwheel.FiveSixths.checked_D7_052 i).1 (RealPinwheel.FiveSixths.checked_D7_052 i).2
          rw [← align_12 i]
          have he : 857 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 913
          ·
            let i : Fin 29 := ⟨j.val - 884, by omega⟩
            apply of_witness A (witnessD7_053 i) 352 (RealPinwheel.FiveSixths.checked_D7_053 i).1 (RealPinwheel.FiveSixths.checked_D7_053 i).2
            rw [← align_13 i]
            have he : 884 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 29 := ⟨j.val - 913, by omega⟩
            apply of_witness A (witnessD7_054 i) 352 (RealPinwheel.FiveSixths.checked_D7_054 i).1 (RealPinwheel.FiveSixths.checked_D7_054 i).2
            rw [← align_14 i]
            have he : 913 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 1001
      ·
        by_cases h15_17 : j.val < 971
        ·
          let i : Fin 29 := ⟨j.val - 942, by omega⟩
          apply of_witness A (witnessD7_055 i) 352 (RealPinwheel.FiveSixths.checked_D7_055 i).1 (RealPinwheel.FiveSixths.checked_D7_055 i).2
          rw [← align_15 i]
          have he : 942 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 30 := ⟨j.val - 971, by omega⟩
          apply of_witness A (witnessD7_056 i) 352 (RealPinwheel.FiveSixths.checked_D7_056 i).1 (RealPinwheel.FiveSixths.checked_D7_056 i).2
          rw [← align_16 i]
          have he : 971 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 1032
        ·
          let i : Fin 31 := ⟨j.val - 1001, by omega⟩
          apply of_witness A (witnessD7_057 i) 352 (RealPinwheel.FiveSixths.checked_D7_057 i).1 (RealPinwheel.FiveSixths.checked_D7_057 i).2
          rw [← align_17 i]
          have he : 1001 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 1063
          ·
            let i : Fin 31 := ⟨j.val - 1032, by omega⟩
            apply of_witness A (witnessD7_058 i) 352 (RealPinwheel.FiveSixths.checked_D7_058 i).1 (RealPinwheel.FiveSixths.checked_D7_058 i).2
            rw [← align_18 i]
            have he : 1032 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 32 := ⟨j.val - 1063, by omega⟩
            apply of_witness A (witnessD7_059 i) 352 (RealPinwheel.FiveSixths.checked_D7_059 i).1 (RealPinwheel.FiveSixths.checked_D7_059 i).2
            rw [← align_19 i]
            have he : 1063 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
