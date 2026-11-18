-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:26:34.994404+00:00
-- url     : https://prove2.me/submissions/3adff3e0-5801-48b3-a4c4-fbba1b5852e7

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_000
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_001
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_002
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_003
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_004
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_005
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_006
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_007
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_008
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_009
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_010
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_011
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_012
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_013
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_014
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_015
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_016
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_017
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_018
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_019
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
    (hlo : 0 ≤ j.val) (hhi : j.val < 51)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 1, codeFunctionD8 (0 + i.val) = (witnessD8_000 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 1, codeFunctionD8 (1 + i.val) = (witnessD8_001 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 1, codeFunctionD8 (2 + i.val) = (witnessD8_002 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 1, codeFunctionD8 (3 + i.val) = (witnessD8_003 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 2, codeFunctionD8 (4 + i.val) = (witnessD8_004 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 2, codeFunctionD8 (6 + i.val) = (witnessD8_005 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 2, codeFunctionD8 (8 + i.val) = (witnessD8_006 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 2, codeFunctionD8 (10 + i.val) = (witnessD8_007 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 2, codeFunctionD8 (12 + i.val) = (witnessD8_008 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 2, codeFunctionD8 (14 + i.val) = (witnessD8_009 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 3, codeFunctionD8 (16 + i.val) = (witnessD8_010 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 3, codeFunctionD8 (19 + i.val) = (witnessD8_011 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 3, codeFunctionD8 (22 + i.val) = (witnessD8_012 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 3, codeFunctionD8 (25 + i.val) = (witnessD8_013 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 3, codeFunctionD8 (28 + i.val) = (witnessD8_014 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 4, codeFunctionD8 (31 + i.val) = (witnessD8_015 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 4, codeFunctionD8 (35 + i.val) = (witnessD8_016 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 4, codeFunctionD8 (39 + i.val) = (witnessD8_017 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 4, codeFunctionD8 (43 + i.val) = (witnessD8_018 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 4, codeFunctionD8 (47 + i.val) = (witnessD8_019 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 16
  ·
    by_cases h0_10 : j.val < 6
    ·
      by_cases h0_5 : j.val < 2
      ·
        by_cases h0_2 : j.val < 1
        ·
          let i : Fin 1 := ⟨j.val - 0, by omega⟩
          apply of_witness A (witnessD8_000 i) 608 (RealPinwheel.FiveSixths.checked_D8_000 i).1 (RealPinwheel.FiveSixths.checked_D8_000 i).2
          rw [← align_0 i]
          have he : 0 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 1 := ⟨j.val - 1, by omega⟩
          apply of_witness A (witnessD8_001 i) 608 (RealPinwheel.FiveSixths.checked_D8_001 i).1 (RealPinwheel.FiveSixths.checked_D8_001 i).2
          rw [← align_1 i]
          have he : 1 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 3
        ·
          let i : Fin 1 := ⟨j.val - 2, by omega⟩
          apply of_witness A (witnessD8_002 i) 608 (RealPinwheel.FiveSixths.checked_D8_002 i).1 (RealPinwheel.FiveSixths.checked_D8_002 i).2
          rw [← align_2 i]
          have he : 2 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 4
          ·
            let i : Fin 1 := ⟨j.val - 3, by omega⟩
            apply of_witness A (witnessD8_003 i) 608 (RealPinwheel.FiveSixths.checked_D8_003 i).1 (RealPinwheel.FiveSixths.checked_D8_003 i).2
            rw [← align_3 i]
            have he : 3 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 2 := ⟨j.val - 4, by omega⟩
            apply of_witness A (witnessD8_004 i) 608 (RealPinwheel.FiveSixths.checked_D8_004 i).1 (RealPinwheel.FiveSixths.checked_D8_004 i).2
            rw [← align_4 i]
            have he : 4 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 10
      ·
        by_cases h5_7 : j.val < 8
        ·
          let i : Fin 2 := ⟨j.val - 6, by omega⟩
          apply of_witness A (witnessD8_005 i) 608 (RealPinwheel.FiveSixths.checked_D8_005 i).1 (RealPinwheel.FiveSixths.checked_D8_005 i).2
          rw [← align_5 i]
          have he : 6 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 2 := ⟨j.val - 8, by omega⟩
          apply of_witness A (witnessD8_006 i) 608 (RealPinwheel.FiveSixths.checked_D8_006 i).1 (RealPinwheel.FiveSixths.checked_D8_006 i).2
          rw [← align_6 i]
          have he : 8 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 12
        ·
          let i : Fin 2 := ⟨j.val - 10, by omega⟩
          apply of_witness A (witnessD8_007 i) 608 (RealPinwheel.FiveSixths.checked_D8_007 i).1 (RealPinwheel.FiveSixths.checked_D8_007 i).2
          rw [← align_7 i]
          have he : 10 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 14
          ·
            let i : Fin 2 := ⟨j.val - 12, by omega⟩
            apply of_witness A (witnessD8_008 i) 608 (RealPinwheel.FiveSixths.checked_D8_008 i).1 (RealPinwheel.FiveSixths.checked_D8_008 i).2
            rw [← align_8 i]
            have he : 12 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 2 := ⟨j.val - 14, by omega⟩
            apply of_witness A (witnessD8_009 i) 608 (RealPinwheel.FiveSixths.checked_D8_009 i).1 (RealPinwheel.FiveSixths.checked_D8_009 i).2
            rw [← align_9 i]
            have he : 14 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 31
    ·
      by_cases h10_15 : j.val < 22
      ·
        by_cases h10_12 : j.val < 19
        ·
          let i : Fin 3 := ⟨j.val - 16, by omega⟩
          apply of_witness A (witnessD8_010 i) 608 (RealPinwheel.FiveSixths.checked_D8_010 i).1 (RealPinwheel.FiveSixths.checked_D8_010 i).2
          rw [← align_10 i]
          have he : 16 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 3 := ⟨j.val - 19, by omega⟩
          apply of_witness A (witnessD8_011 i) 608 (RealPinwheel.FiveSixths.checked_D8_011 i).1 (RealPinwheel.FiveSixths.checked_D8_011 i).2
          rw [← align_11 i]
          have he : 19 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 25
        ·
          let i : Fin 3 := ⟨j.val - 22, by omega⟩
          apply of_witness A (witnessD8_012 i) 608 (RealPinwheel.FiveSixths.checked_D8_012 i).1 (RealPinwheel.FiveSixths.checked_D8_012 i).2
          rw [← align_12 i]
          have he : 22 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 28
          ·
            let i : Fin 3 := ⟨j.val - 25, by omega⟩
            apply of_witness A (witnessD8_013 i) 608 (RealPinwheel.FiveSixths.checked_D8_013 i).1 (RealPinwheel.FiveSixths.checked_D8_013 i).2
            rw [← align_13 i]
            have he : 25 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 3 := ⟨j.val - 28, by omega⟩
            apply of_witness A (witnessD8_014 i) 608 (RealPinwheel.FiveSixths.checked_D8_014 i).1 (RealPinwheel.FiveSixths.checked_D8_014 i).2
            rw [← align_14 i]
            have he : 28 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 39
      ·
        by_cases h15_17 : j.val < 35
        ·
          let i : Fin 4 := ⟨j.val - 31, by omega⟩
          apply of_witness A (witnessD8_015 i) 608 (RealPinwheel.FiveSixths.checked_D8_015 i).1 (RealPinwheel.FiveSixths.checked_D8_015 i).2
          rw [← align_15 i]
          have he : 31 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 4 := ⟨j.val - 35, by omega⟩
          apply of_witness A (witnessD8_016 i) 608 (RealPinwheel.FiveSixths.checked_D8_016 i).1 (RealPinwheel.FiveSixths.checked_D8_016 i).2
          rw [← align_16 i]
          have he : 35 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 43
        ·
          let i : Fin 4 := ⟨j.val - 39, by omega⟩
          apply of_witness A (witnessD8_017 i) 608 (RealPinwheel.FiveSixths.checked_D8_017 i).1 (RealPinwheel.FiveSixths.checked_D8_017 i).2
          rw [← align_17 i]
          have he : 39 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 47
          ·
            let i : Fin 4 := ⟨j.val - 43, by omega⟩
            apply of_witness A (witnessD8_018 i) 608 (RealPinwheel.FiveSixths.checked_D8_018 i).1 (RealPinwheel.FiveSixths.checked_D8_018 i).2
            rw [← align_18 i]
            have he : 43 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 4 := ⟨j.val - 47, by omega⟩
            apply of_witness A (witnessD8_019 i) 608 (RealPinwheel.FiveSixths.checked_D8_019 i).1 (RealPinwheel.FiveSixths.checked_D8_019 i).2
            rw [← align_19 i]
            have he : 47 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
