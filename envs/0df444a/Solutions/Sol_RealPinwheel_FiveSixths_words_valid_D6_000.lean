-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D6_000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:55:40.865142+00:00
-- url     : https://prove2.me/submissions/bd882690-ee8d-46d7-b23a-d40d0454c88b

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD6
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_000
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_001
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_002
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_003
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_004
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_005
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_006
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_007
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_008
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_009
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_010
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_011
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_012
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_013
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_014
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_015
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_016
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_017
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

theorem solution (A : Instance 6) (j : Fin 630)
    (hlo : 0 ≤ j.val) (hhi : j.val < 630)
    (hb : codeBox (codeFunctionD6 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 6), 0 < L ∧ L ≤ 64 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 16, codeFunctionD6 (0 + i.val) = (witnessD6_000 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 19, codeFunctionD6 (16 + i.val) = (witnessD6_001 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 21, codeFunctionD6 (35 + i.val) = (witnessD6_002 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 23, codeFunctionD6 (56 + i.val) = (witnessD6_003 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 26, codeFunctionD6 (79 + i.val) = (witnessD6_004 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 27, codeFunctionD6 (105 + i.val) = (witnessD6_005 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 29, codeFunctionD6 (132 + i.val) = (witnessD6_006 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 30, codeFunctionD6 (161 + i.val) = (witnessD6_007 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 31, codeFunctionD6 (191 + i.val) = (witnessD6_008 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 33, codeFunctionD6 (222 + i.val) = (witnessD6_009 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 35, codeFunctionD6 (255 + i.val) = (witnessD6_010 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 39, codeFunctionD6 (290 + i.val) = (witnessD6_011 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 43, codeFunctionD6 (329 + i.val) = (witnessD6_012 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_13 : ∀ i : Fin 48, codeFunctionD6 (372 + i.val) = (witnessD6_013 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_14 : ∀ i : Fin 52, codeFunctionD6 (420 + i.val) = (witnessD6_014 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_15 : ∀ i : Fin 57, codeFunctionD6 (472 + i.val) = (witnessD6_015 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_16 : ∀ i : Fin 65, codeFunctionD6 (529 + i.val) = (witnessD6_016 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_17 : ∀ i : Fin 36, codeFunctionD6 (594 + i.val) = (witnessD6_017 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_18 : j.val < 222
  ·
    by_cases h0_9 : j.val < 79
    ·
      by_cases h0_4 : j.val < 35
      ·
        by_cases h0_2 : j.val < 16
        ·
          let i : Fin 16 := ⟨j.val - 0, by omega⟩
          apply of_witness A (witnessD6_000 i) 64 (RealPinwheel.FiveSixths.checked_D6_000 i).1 (RealPinwheel.FiveSixths.checked_D6_000 i).2
          rw [← align_0 i]
          have he : 0 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 19 := ⟨j.val - 16, by omega⟩
          apply of_witness A (witnessD6_001 i) 64 (RealPinwheel.FiveSixths.checked_D6_001 i).1 (RealPinwheel.FiveSixths.checked_D6_001 i).2
          rw [← align_1 i]
          have he : 16 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h2_4 : j.val < 56
        ·
          let i : Fin 21 := ⟨j.val - 35, by omega⟩
          apply of_witness A (witnessD6_002 i) 64 (RealPinwheel.FiveSixths.checked_D6_002 i).1 (RealPinwheel.FiveSixths.checked_D6_002 i).2
          rw [← align_2 i]
          have he : 35 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 23 := ⟨j.val - 56, by omega⟩
          apply of_witness A (witnessD6_003 i) 64 (RealPinwheel.FiveSixths.checked_D6_003 i).1 (RealPinwheel.FiveSixths.checked_D6_003 i).2
          rw [← align_3 i]
          have he : 56 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
    ·
      by_cases h4_9 : j.val < 132
      ·
        by_cases h4_6 : j.val < 105
        ·
          let i : Fin 26 := ⟨j.val - 79, by omega⟩
          apply of_witness A (witnessD6_004 i) 64 (RealPinwheel.FiveSixths.checked_D6_004 i).1 (RealPinwheel.FiveSixths.checked_D6_004 i).2
          rw [← align_4 i]
          have he : 79 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 27 := ⟨j.val - 105, by omega⟩
          apply of_witness A (witnessD6_005 i) 64 (RealPinwheel.FiveSixths.checked_D6_005 i).1 (RealPinwheel.FiveSixths.checked_D6_005 i).2
          rw [← align_5 i]
          have he : 105 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h6_9 : j.val < 161
        ·
          let i : Fin 29 := ⟨j.val - 132, by omega⟩
          apply of_witness A (witnessD6_006 i) 64 (RealPinwheel.FiveSixths.checked_D6_006 i).1 (RealPinwheel.FiveSixths.checked_D6_006 i).2
          rw [← align_6 i]
          have he : 132 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h7_9 : j.val < 191
          ·
            let i : Fin 30 := ⟨j.val - 161, by omega⟩
            apply of_witness A (witnessD6_007 i) 64 (RealPinwheel.FiveSixths.checked_D6_007 i).1 (RealPinwheel.FiveSixths.checked_D6_007 i).2
            rw [← align_7 i]
            have he : 161 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 31 := ⟨j.val - 191, by omega⟩
            apply of_witness A (witnessD6_008 i) 64 (RealPinwheel.FiveSixths.checked_D6_008 i).1 (RealPinwheel.FiveSixths.checked_D6_008 i).2
            rw [← align_8 i]
            have he : 191 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
  ·
    by_cases h9_18 : j.val < 372
    ·
      by_cases h9_13 : j.val < 290
      ·
        by_cases h9_11 : j.val < 255
        ·
          let i : Fin 33 := ⟨j.val - 222, by omega⟩
          apply of_witness A (witnessD6_009 i) 64 (RealPinwheel.FiveSixths.checked_D6_009 i).1 (RealPinwheel.FiveSixths.checked_D6_009 i).2
          rw [← align_9 i]
          have he : 222 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 35 := ⟨j.val - 255, by omega⟩
          apply of_witness A (witnessD6_010 i) 64 (RealPinwheel.FiveSixths.checked_D6_010 i).1 (RealPinwheel.FiveSixths.checked_D6_010 i).2
          rw [← align_10 i]
          have he : 255 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h11_13 : j.val < 329
        ·
          let i : Fin 39 := ⟨j.val - 290, by omega⟩
          apply of_witness A (witnessD6_011 i) 64 (RealPinwheel.FiveSixths.checked_D6_011 i).1 (RealPinwheel.FiveSixths.checked_D6_011 i).2
          rw [← align_11 i]
          have he : 290 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 43 := ⟨j.val - 329, by omega⟩
          apply of_witness A (witnessD6_012 i) 64 (RealPinwheel.FiveSixths.checked_D6_012 i).1 (RealPinwheel.FiveSixths.checked_D6_012 i).2
          rw [← align_12 i]
          have he : 329 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
    ·
      by_cases h13_18 : j.val < 472
      ·
        by_cases h13_15 : j.val < 420
        ·
          let i : Fin 48 := ⟨j.val - 372, by omega⟩
          apply of_witness A (witnessD6_013 i) 64 (RealPinwheel.FiveSixths.checked_D6_013 i).1 (RealPinwheel.FiveSixths.checked_D6_013 i).2
          rw [← align_13 i]
          have he : 372 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 52 := ⟨j.val - 420, by omega⟩
          apply of_witness A (witnessD6_014 i) 64 (RealPinwheel.FiveSixths.checked_D6_014 i).1 (RealPinwheel.FiveSixths.checked_D6_014 i).2
          rw [← align_14 i]
          have he : 420 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h15_18 : j.val < 529
        ·
          let i : Fin 57 := ⟨j.val - 472, by omega⟩
          apply of_witness A (witnessD6_015 i) 64 (RealPinwheel.FiveSixths.checked_D6_015 i).1 (RealPinwheel.FiveSixths.checked_D6_015 i).2
          rw [← align_15 i]
          have he : 472 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          by_cases h16_18 : j.val < 594
          ·
            let i : Fin 65 := ⟨j.val - 529, by omega⟩
            apply of_witness A (witnessD6_016 i) 64 (RealPinwheel.FiveSixths.checked_D6_016 i).1 (RealPinwheel.FiveSixths.checked_D6_016 i).2
            rw [← align_16 i]
            have he : 529 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
          ·
            let i : Fin 36 := ⟨j.val - 594, by omega⟩
            apply of_witness A (witnessD6_017 i) 64 (RealPinwheel.FiveSixths.checked_D6_017 i).1 (RealPinwheel.FiveSixths.checked_D6_017 i).2
            rw [← align_17 i]
            have he : 594 + i.val = j.val := by dsimp [i]; omega
            rw [he]
            exact hb
