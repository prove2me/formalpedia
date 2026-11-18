-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D5_000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:18.175088+00:00
-- url     : https://prove2.me/submissions/3dc0756b-d0be-47f9-97e6-02817aae5ede

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD5
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D5_000
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D5_001
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D5_002
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D5_003
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

theorem solution (A : Instance 5) (j : Fin 216)
    (hlo : 0 ≤ j.val) (hhi : j.val < 216)
    (hb : codeBox (codeFunctionD5 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 5), 0 < L ∧ L ≤ 32 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 36, codeFunctionD5 (0 + i.val) = (witnessD5_000 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 50, codeFunctionD5 (36 + i.val) = (witnessD5_001 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 61, codeFunctionD5 (86 + i.val) = (witnessD5_002 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 69, codeFunctionD5 (147 + i.val) = (witnessD5_003 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_4 : j.val < 86
  ·
    by_cases h0_2 : j.val < 36
    ·
      let i : Fin 36 := ⟨j.val - 0, by omega⟩
      apply of_witness A (witnessD5_000 i) 32 (RealPinwheel.FiveSixths.checked_D5_000 i).1 (RealPinwheel.FiveSixths.checked_D5_000 i).2
      rw [← align_0 i]
      have he : 0 + i.val = j.val := by dsimp [i]; omega
      rw [he]
      exact hb
    ·
      let i : Fin 50 := ⟨j.val - 36, by omega⟩
      apply of_witness A (witnessD5_001 i) 32 (RealPinwheel.FiveSixths.checked_D5_001 i).1 (RealPinwheel.FiveSixths.checked_D5_001 i).2
      rw [← align_1 i]
      have he : 36 + i.val = j.val := by dsimp [i]; omega
      rw [he]
      exact hb
  ·
    by_cases h2_4 : j.val < 147
    ·
      let i : Fin 61 := ⟨j.val - 86, by omega⟩
      apply of_witness A (witnessD5_002 i) 32 (RealPinwheel.FiveSixths.checked_D5_002 i).1 (RealPinwheel.FiveSixths.checked_D5_002 i).2
      rw [← align_2 i]
      have he : 86 + i.val = j.val := by dsimp [i]; omega
      rw [he]
      exact hb
    ·
      let i : Fin 69 := ⟨j.val - 147, by omega⟩
      apply of_witness A (witnessD5_003 i) 32 (RealPinwheel.FiveSixths.checked_D5_003 i).1 (RealPinwheel.FiveSixths.checked_D5_003 i).2
      rw [← align_3 i]
      have he : 147 + i.val = j.val := by dsimp [i]; omega
      rw [he]
      exact hb
