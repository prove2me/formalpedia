-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:50:40.527196+00:00
-- url     : https://prove2.me/submissions/c42a3ae0-7d1e-4ca8-92db-3ca10b424758

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_000
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_001
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_002
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_003
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_004
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_005
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_006
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_007
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_008
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_009
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_010
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_011
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_012
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_013
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_014
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_015
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_016
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_017
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_018
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_019
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
    (hlo : 0 ≤ j.val) (hhi : j.val < 32)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 1, codeFunctionP9 (0 + i.val) = (witnessP9_000 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 1, codeFunctionP9 (1 + i.val) = (witnessP9_001 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 1, codeFunctionP9 (2 + i.val) = (witnessP9_002 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 1, codeFunctionP9 (3 + i.val) = (witnessP9_003 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 1, codeFunctionP9 (4 + i.val) = (witnessP9_004 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 1, codeFunctionP9 (5 + i.val) = (witnessP9_005 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 1, codeFunctionP9 (6 + i.val) = (witnessP9_006 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 1, codeFunctionP9 (7 + i.val) = (witnessP9_007 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 1, codeFunctionP9 (8 + i.val) = (witnessP9_008 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 2, codeFunctionP9 (9 + i.val) = (witnessP9_009 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 2, codeFunctionP9 (11 + i.val) = (witnessP9_010 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 2, codeFunctionP9 (13 + i.val) = (witnessP9_011 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 2, codeFunctionP9 (15 + i.val) = (witnessP9_012 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 2, codeFunctionP9 (17 + i.val) = (witnessP9_013 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 2, codeFunctionP9 (19 + i.val) = (witnessP9_014 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 2, codeFunctionP9 (21 + i.val) = (witnessP9_015 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 2, codeFunctionP9 (23 + i.val) = (witnessP9_016 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 2, codeFunctionP9 (25 + i.val) = (witnessP9_017 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_18 : ∀ i : Fin 2, codeFunctionP9 (27 + i.val) = (witnessP9_018 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_19 : ∀ i : Fin 3, codeFunctionP9 (29 + i.val) = (witnessP9_019 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_20 : j.val < 11
  ·
    by_cases h0_10 : j.val < 5
    ·
      by_cases h0_5 : j.val < 2
      ·
        by_cases h0_2 : j.val < 1
        ·
          let i : Fin 1 := ⟨j.val - 0, by omega⟩
          apply of_witness A (witnessP9_000 i) 1800 (RealPinwheel.FiveSixths.checked_P9_000 i).1 (RealPinwheel.FiveSixths.checked_P9_000 i).2
          rw [← align_0 i]
          have he : 0 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 1 := ⟨j.val - 1, by omega⟩
          apply of_witness A (witnessP9_001 i) 1800 (RealPinwheel.FiveSixths.checked_P9_001 i).1 (RealPinwheel.FiveSixths.checked_P9_001 i).2
          rw [← align_1 i]
          have he : 1 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_5 : j.val < 3
        ·
          let i : Fin 1 := ⟨j.val - 2, by omega⟩
          apply of_witness A (witnessP9_002 i) 1800 (RealPinwheel.FiveSixths.checked_P9_002 i).1 (RealPinwheel.FiveSixths.checked_P9_002 i).2
          rw [← align_2 i]
          have he : 2 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h3_5 : j.val < 4
          ·
            let i : Fin 1 := ⟨j.val - 3, by omega⟩
            apply of_witness A (witnessP9_003 i) 1800 (RealPinwheel.FiveSixths.checked_P9_003 i).1 (RealPinwheel.FiveSixths.checked_P9_003 i).2
            rw [← align_3 i]
            have he : 3 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 1 := ⟨j.val - 4, by omega⟩
            apply of_witness A (witnessP9_004 i) 1800 (RealPinwheel.FiveSixths.checked_P9_004 i).1 (RealPinwheel.FiveSixths.checked_P9_004 i).2
            rw [← align_4 i]
            have he : 4 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h5_10 : j.val < 7
      ·
        by_cases h5_7 : j.val < 6
        ·
          let i : Fin 1 := ⟨j.val - 5, by omega⟩
          apply of_witness A (witnessP9_005 i) 1800 (RealPinwheel.FiveSixths.checked_P9_005 i).1 (RealPinwheel.FiveSixths.checked_P9_005 i).2
          rw [← align_5 i]
          have he : 5 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 1 := ⟨j.val - 6, by omega⟩
          apply of_witness A (witnessP9_006 i) 1800 (RealPinwheel.FiveSixths.checked_P9_006 i).1 (RealPinwheel.FiveSixths.checked_P9_006 i).2
          rw [← align_6 i]
          have he : 6 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h7_10 : j.val < 8
        ·
          let i : Fin 1 := ⟨j.val - 7, by omega⟩
          apply of_witness A (witnessP9_007 i) 1800 (RealPinwheel.FiveSixths.checked_P9_007 i).1 (RealPinwheel.FiveSixths.checked_P9_007 i).2
          rw [← align_7 i]
          have he : 7 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h8_10 : j.val < 9
          ·
            let i : Fin 1 := ⟨j.val - 8, by omega⟩
            apply of_witness A (witnessP9_008 i) 1800 (RealPinwheel.FiveSixths.checked_P9_008 i).1 (RealPinwheel.FiveSixths.checked_P9_008 i).2
            rw [← align_8 i]
            have he : 8 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 2 := ⟨j.val - 9, by omega⟩
            apply of_witness A (witnessP9_009 i) 1800 (RealPinwheel.FiveSixths.checked_P9_009 i).1 (RealPinwheel.FiveSixths.checked_P9_009 i).2
            rw [← align_9 i]
            have he : 9 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h10_20 : j.val < 21
    ·
      by_cases h10_15 : j.val < 15
      ·
        by_cases h10_12 : j.val < 13
        ·
          let i : Fin 2 := ⟨j.val - 11, by omega⟩
          apply of_witness A (witnessP9_010 i) 1800 (RealPinwheel.FiveSixths.checked_P9_010 i).1 (RealPinwheel.FiveSixths.checked_P9_010 i).2
          rw [← align_10 i]
          have he : 11 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 2 := ⟨j.val - 13, by omega⟩
          apply of_witness A (witnessP9_011 i) 1800 (RealPinwheel.FiveSixths.checked_P9_011 i).1 (RealPinwheel.FiveSixths.checked_P9_011 i).2
          rw [← align_11 i]
          have he : 13 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h12_15 : j.val < 17
        ·
          let i : Fin 2 := ⟨j.val - 15, by omega⟩
          apply of_witness A (witnessP9_012 i) 1800 (RealPinwheel.FiveSixths.checked_P9_012 i).1 (RealPinwheel.FiveSixths.checked_P9_012 i).2
          rw [← align_12 i]
          have he : 15 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h13_15 : j.val < 19
          ·
            let i : Fin 2 := ⟨j.val - 17, by omega⟩
            apply of_witness A (witnessP9_013 i) 1800 (RealPinwheel.FiveSixths.checked_P9_013 i).1 (RealPinwheel.FiveSixths.checked_P9_013 i).2
            rw [← align_13 i]
            have he : 17 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 2 := ⟨j.val - 19, by omega⟩
            apply of_witness A (witnessP9_014 i) 1800 (RealPinwheel.FiveSixths.checked_P9_014 i).1 (RealPinwheel.FiveSixths.checked_P9_014 i).2
            rw [← align_14 i]
            have he : 19 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
    ·
      by_cases h15_20 : j.val < 25
      ·
        by_cases h15_17 : j.val < 23
        ·
          let i : Fin 2 := ⟨j.val - 21, by omega⟩
          apply of_witness A (witnessP9_015 i) 1800 (RealPinwheel.FiveSixths.checked_P9_015 i).1 (RealPinwheel.FiveSixths.checked_P9_015 i).2
          rw [← align_15 i]
          have he : 21 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 2 := ⟨j.val - 23, by omega⟩
          apply of_witness A (witnessP9_016 i) 1800 (RealPinwheel.FiveSixths.checked_P9_016 i).1 (RealPinwheel.FiveSixths.checked_P9_016 i).2
          rw [← align_16 i]
          have he : 23 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h17_20 : j.val < 27
        ·
          let i : Fin 2 := ⟨j.val - 25, by omega⟩
          apply of_witness A (witnessP9_017 i) 1800 (RealPinwheel.FiveSixths.checked_P9_017 i).1 (RealPinwheel.FiveSixths.checked_P9_017 i).2
          rw [← align_17 i]
          have he : 25 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h18_20 : j.val < 29
          ·
            let i : Fin 2 := ⟨j.val - 27, by omega⟩
            apply of_witness A (witnessP9_018 i) 1800 (RealPinwheel.FiveSixths.checked_P9_018 i).1 (RealPinwheel.FiveSixths.checked_P9_018 i).2
            rw [← align_18 i]
            have he : 27 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 3 := ⟨j.val - 29, by omega⟩
            apply of_witness A (witnessP9_019 i) 1800 (RealPinwheel.FiveSixths.checked_P9_019 i).1 (RealPinwheel.FiveSixths.checked_P9_019 i).2
            rw [← align_19 i]
            have he : 29 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
