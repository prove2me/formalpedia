-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D7_000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:42:38.265222+00:00
-- url     : https://prove2.me/submissions/d3b8dd89-3a17-436c-a407-e5a1466c7a5e

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD7
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_000
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_001
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_002
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_003
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_004
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_005
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_006
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_007
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_008
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_009
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_010
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_011
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_012
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_013
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_014
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_015
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_016
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_017
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_018
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_019
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
    (hlo : 0 ≤ j.val) (hhi : j.val < 196)
    (hb : codeBox (codeFunctionD7 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 7), 0 < L ∧ L ≤ 352 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 3, codeFunctionD7 (0 + i.val) = (witnessD7_000 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 5, codeFunctionD7 (3 + i.val) = (witnessD7_001 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 6, codeFunctionD7 (8 + i.val) = (witnessD7_002 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 7, codeFunctionD7 (14 + i.val) = (witnessD7_003 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 8, codeFunctionD7 (21 + i.val) = (witnessD7_004 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 8, codeFunctionD7 (29 + i.val) = (witnessD7_005 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 9, codeFunctionD7 (37 + i.val) = (witnessD7_006 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 9, codeFunctionD7 (46 + i.val) = (witnessD7_007 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 10, codeFunctionD7 (55 + i.val) = (witnessD7_008 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 10, codeFunctionD7 (65 + i.val) = (witnessD7_009 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 10, codeFunctionD7 (75 + i.val) = (witnessD7_010 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 11, codeFunctionD7 (85 + i.val) = (witnessD7_011 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 11, codeFunctionD7 (96 + i.val) = (witnessD7_012 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 11, codeFunctionD7 (107 + i.val) = (witnessD7_013 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 12, codeFunctionD7 (118 + i.val) = (witnessD7_014 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 12, codeFunctionD7 (130 + i.val) = (witnessD7_015 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 13, codeFunctionD7 (142 + i.val) = (witnessD7_016 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 13, codeFunctionD7 (155 + i.val) = (witnessD7_017 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 14, codeFunctionD7 (168 + i.val) = (witnessD7_018 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 14, codeFunctionD7 (182 + i.val) = (witnessD7_019 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 75
  ·
    by_cases h0_10 : j.val < 29
    ·
      by_cases h0_5 : j.val < 8
      ·
        by_cases h0_2 : j.val < 3
        ·
          let i : Fin 3 := ⟨j.val - 0, by omega⟩
          apply of_witness A (witnessD7_000 i) 352 (RealPinwheel.FiveSixths.checked_D7_000 i).1 (RealPinwheel.FiveSixths.checked_D7_000 i).2
          rw [← align_0 i]
          have he : 0 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 5 := ⟨j.val - 3, by omega⟩
          apply of_witness A (witnessD7_001 i) 352 (RealPinwheel.FiveSixths.checked_D7_001 i).1 (RealPinwheel.FiveSixths.checked_D7_001 i).2
          rw [← align_1 i]
          have he : 3 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 14
        ·
          let i : Fin 6 := ⟨j.val - 8, by omega⟩
          apply of_witness A (witnessD7_002 i) 352 (RealPinwheel.FiveSixths.checked_D7_002 i).1 (RealPinwheel.FiveSixths.checked_D7_002 i).2
          rw [← align_2 i]
          have he : 8 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 21
          ·
            let i : Fin 7 := ⟨j.val - 14, by omega⟩
            apply of_witness A (witnessD7_003 i) 352 (RealPinwheel.FiveSixths.checked_D7_003 i).1 (RealPinwheel.FiveSixths.checked_D7_003 i).2
            rw [← align_3 i]
            have he : 14 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 8 := ⟨j.val - 21, by omega⟩
            apply of_witness A (witnessD7_004 i) 352 (RealPinwheel.FiveSixths.checked_D7_004 i).1 (RealPinwheel.FiveSixths.checked_D7_004 i).2
            rw [← align_4 i]
            have he : 21 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 46
      ·
        by_cases h5_7 : j.val < 37
        ·
          let i : Fin 8 := ⟨j.val - 29, by omega⟩
          apply of_witness A (witnessD7_005 i) 352 (RealPinwheel.FiveSixths.checked_D7_005 i).1 (RealPinwheel.FiveSixths.checked_D7_005 i).2
          rw [← align_5 i]
          have he : 29 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 9 := ⟨j.val - 37, by omega⟩
          apply of_witness A (witnessD7_006 i) 352 (RealPinwheel.FiveSixths.checked_D7_006 i).1 (RealPinwheel.FiveSixths.checked_D7_006 i).2
          rw [← align_6 i]
          have he : 37 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 55
        ·
          let i : Fin 9 := ⟨j.val - 46, by omega⟩
          apply of_witness A (witnessD7_007 i) 352 (RealPinwheel.FiveSixths.checked_D7_007 i).1 (RealPinwheel.FiveSixths.checked_D7_007 i).2
          rw [← align_7 i]
          have he : 46 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 65
          ·
            let i : Fin 10 := ⟨j.val - 55, by omega⟩
            apply of_witness A (witnessD7_008 i) 352 (RealPinwheel.FiveSixths.checked_D7_008 i).1 (RealPinwheel.FiveSixths.checked_D7_008 i).2
            rw [← align_8 i]
            have he : 55 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 10 := ⟨j.val - 65, by omega⟩
            apply of_witness A (witnessD7_009 i) 352 (RealPinwheel.FiveSixths.checked_D7_009 i).1 (RealPinwheel.FiveSixths.checked_D7_009 i).2
            rw [← align_9 i]
            have he : 65 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 130
    ·
      by_cases h10_15 : j.val < 96
      ·
        by_cases h10_12 : j.val < 85
        ·
          let i : Fin 10 := ⟨j.val - 75, by omega⟩
          apply of_witness A (witnessD7_010 i) 352 (RealPinwheel.FiveSixths.checked_D7_010 i).1 (RealPinwheel.FiveSixths.checked_D7_010 i).2
          rw [← align_10 i]
          have he : 75 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 11 := ⟨j.val - 85, by omega⟩
          apply of_witness A (witnessD7_011 i) 352 (RealPinwheel.FiveSixths.checked_D7_011 i).1 (RealPinwheel.FiveSixths.checked_D7_011 i).2
          rw [← align_11 i]
          have he : 85 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 107
        ·
          let i : Fin 11 := ⟨j.val - 96, by omega⟩
          apply of_witness A (witnessD7_012 i) 352 (RealPinwheel.FiveSixths.checked_D7_012 i).1 (RealPinwheel.FiveSixths.checked_D7_012 i).2
          rw [← align_12 i]
          have he : 96 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 118
          ·
            let i : Fin 11 := ⟨j.val - 107, by omega⟩
            apply of_witness A (witnessD7_013 i) 352 (RealPinwheel.FiveSixths.checked_D7_013 i).1 (RealPinwheel.FiveSixths.checked_D7_013 i).2
            rw [← align_13 i]
            have he : 107 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 12 := ⟨j.val - 118, by omega⟩
            apply of_witness A (witnessD7_014 i) 352 (RealPinwheel.FiveSixths.checked_D7_014 i).1 (RealPinwheel.FiveSixths.checked_D7_014 i).2
            rw [← align_14 i]
            have he : 118 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 155
      ·
        by_cases h15_17 : j.val < 142
        ·
          let i : Fin 12 := ⟨j.val - 130, by omega⟩
          apply of_witness A (witnessD7_015 i) 352 (RealPinwheel.FiveSixths.checked_D7_015 i).1 (RealPinwheel.FiveSixths.checked_D7_015 i).2
          rw [← align_15 i]
          have he : 130 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 13 := ⟨j.val - 142, by omega⟩
          apply of_witness A (witnessD7_016 i) 352 (RealPinwheel.FiveSixths.checked_D7_016 i).1 (RealPinwheel.FiveSixths.checked_D7_016 i).2
          rw [← align_16 i]
          have he : 142 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 168
        ·
          let i : Fin 13 := ⟨j.val - 155, by omega⟩
          apply of_witness A (witnessD7_017 i) 352 (RealPinwheel.FiveSixths.checked_D7_017 i).1 (RealPinwheel.FiveSixths.checked_D7_017 i).2
          rw [← align_17 i]
          have he : 155 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 182
          ·
            let i : Fin 14 := ⟨j.val - 168, by omega⟩
            apply of_witness A (witnessD7_018 i) 352 (RealPinwheel.FiveSixths.checked_D7_018 i).1 (RealPinwheel.FiveSixths.checked_D7_018 i).2
            rw [← align_18 i]
            have he : 168 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 14 := ⟨j.val - 182, by omega⟩
            apply of_witness A (witnessD7_019 i) 352 (RealPinwheel.FiveSixths.checked_D7_019 i).1 (RealPinwheel.FiveSixths.checked_D7_019 i).2
            rw [← align_19 i]
            have he : 182 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
