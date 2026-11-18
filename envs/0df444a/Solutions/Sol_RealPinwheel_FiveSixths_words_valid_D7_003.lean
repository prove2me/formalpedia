-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D7_003
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:39:09.39837+00:00
-- url     : https://prove2.me/submissions/10b3d326-80c8-42ad-8ed7-2cbfcb5bb350

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD7
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_060
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_061
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_062
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_063
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_064
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_065
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_066
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_067
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_068
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_069
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_070
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_071
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_072
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
    (hlo : 1095 ≤ j.val) (hhi : j.val < 1657)
    (hb : codeBox (codeFunctionD7 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 7), 0 < L ∧ L ≤ 352 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 33, codeFunctionD7 (1095 + i.val) = (witnessD7_060 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 33, codeFunctionD7 (1128 + i.val) = (witnessD7_061 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 35, codeFunctionD7 (1161 + i.val) = (witnessD7_062 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 35, codeFunctionD7 (1196 + i.val) = (witnessD7_063 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 36, codeFunctionD7 (1231 + i.val) = (witnessD7_064 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_5 : ∀ i : Fin 38, codeFunctionD7 (1267 + i.val) = (witnessD7_065 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_6 : ∀ i : Fin 40, codeFunctionD7 (1305 + i.val) = (witnessD7_066 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_7 : ∀ i : Fin 42, codeFunctionD7 (1345 + i.val) = (witnessD7_067 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_8 : ∀ i : Fin 46, codeFunctionD7 (1387 + i.val) = (witnessD7_068 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_9 : ∀ i : Fin 49, codeFunctionD7 (1433 + i.val) = (witnessD7_069 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_10 : ∀ i : Fin 53, codeFunctionD7 (1482 + i.val) = (witnessD7_070 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_11 : ∀ i : Fin 58, codeFunctionD7 (1535 + i.val) = (witnessD7_071 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_12 : ∀ i : Fin 64, codeFunctionD7 (1593 + i.val) = (witnessD7_072 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_13 : j.val < 1305
  ·
    by_cases h0_6 : j.val < 1196
    ·
      by_cases h0_3 : j.val < 1128
      ·
        let i : Fin 33 := ⟨j.val - 1095, by omega⟩
        apply of_witness A (witnessD7_060 i) 352 (RealPinwheel.FiveSixths.checked_D7_060 i).1 (RealPinwheel.FiveSixths.checked_D7_060 i).2
        rw [← align_0 i]
        have he : 1095 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
      ·
        by_cases h1_3 : j.val < 1161
        ·
          let i : Fin 33 := ⟨j.val - 1128, by omega⟩
          apply of_witness A (witnessD7_061 i) 352 (RealPinwheel.FiveSixths.checked_D7_061 i).1 (RealPinwheel.FiveSixths.checked_D7_061 i).2
          rw [← align_1 i]
          have he : 1128 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 35 := ⟨j.val - 1161, by omega⟩
          apply of_witness A (witnessD7_062 i) 352 (RealPinwheel.FiveSixths.checked_D7_062 i).1 (RealPinwheel.FiveSixths.checked_D7_062 i).2
          rw [← align_2 i]
          have he : 1161 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
    ·
      by_cases h3_6 : j.val < 1231
      ·
        let i : Fin 35 := ⟨j.val - 1196, by omega⟩
        apply of_witness A (witnessD7_063 i) 352 (RealPinwheel.FiveSixths.checked_D7_063 i).1 (RealPinwheel.FiveSixths.checked_D7_063 i).2
        rw [← align_3 i]
        have he : 1196 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
      ·
        by_cases h4_6 : j.val < 1267
        ·
          let i : Fin 36 := ⟨j.val - 1231, by omega⟩
          apply of_witness A (witnessD7_064 i) 352 (RealPinwheel.FiveSixths.checked_D7_064 i).1 (RealPinwheel.FiveSixths.checked_D7_064 i).2
          rw [← align_4 i]
          have he : 1231 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 38 := ⟨j.val - 1267, by omega⟩
          apply of_witness A (witnessD7_065 i) 352 (RealPinwheel.FiveSixths.checked_D7_065 i).1 (RealPinwheel.FiveSixths.checked_D7_065 i).2
          rw [← align_5 i]
          have he : 1267 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
  ·
    by_cases h6_13 : j.val < 1433
    ·
      by_cases h6_9 : j.val < 1345
      ·
        let i : Fin 40 := ⟨j.val - 1305, by omega⟩
        apply of_witness A (witnessD7_066 i) 352 (RealPinwheel.FiveSixths.checked_D7_066 i).1 (RealPinwheel.FiveSixths.checked_D7_066 i).2
        rw [← align_6 i]
        have he : 1305 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
      ·
        by_cases h7_9 : j.val < 1387
        ·
          let i : Fin 42 := ⟨j.val - 1345, by omega⟩
          apply of_witness A (witnessD7_067 i) 352 (RealPinwheel.FiveSixths.checked_D7_067 i).1 (RealPinwheel.FiveSixths.checked_D7_067 i).2
          rw [← align_7 i]
          have he : 1345 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 46 := ⟨j.val - 1387, by omega⟩
          apply of_witness A (witnessD7_068 i) 352 (RealPinwheel.FiveSixths.checked_D7_068 i).1 (RealPinwheel.FiveSixths.checked_D7_068 i).2
          rw [← align_8 i]
          have he : 1387 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
    ·
      by_cases h9_13 : j.val < 1535
      ·
        by_cases h9_11 : j.val < 1482
        ·
          let i : Fin 49 := ⟨j.val - 1433, by omega⟩
          apply of_witness A (witnessD7_069 i) 352 (RealPinwheel.FiveSixths.checked_D7_069 i).1 (RealPinwheel.FiveSixths.checked_D7_069 i).2
          rw [← align_9 i]
          have he : 1433 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 53 := ⟨j.val - 1482, by omega⟩
          apply of_witness A (witnessD7_070 i) 352 (RealPinwheel.FiveSixths.checked_D7_070 i).1 (RealPinwheel.FiveSixths.checked_D7_070 i).2
          rw [← align_10 i]
          have he : 1482 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
      ·
        by_cases h11_13 : j.val < 1593
        ·
          let i : Fin 58 := ⟨j.val - 1535, by omega⟩
          apply of_witness A (witnessD7_071 i) 352 (RealPinwheel.FiveSixths.checked_D7_071 i).1 (RealPinwheel.FiveSixths.checked_D7_071 i).2
          rw [← align_11 i]
          have he : 1535 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
        ·
          let i : Fin 64 := ⟨j.val - 1593, by omega⟩
          apply of_witness A (witnessD7_072 i) 352 (RealPinwheel.FiveSixths.checked_D7_072 i).1 (RealPinwheel.FiveSixths.checked_D7_072 i).2
          rw [← align_12 i]
          have he : 1593 + i.val = j.val := by dsimp [i]; omega
          rw [he]
          exact hb
