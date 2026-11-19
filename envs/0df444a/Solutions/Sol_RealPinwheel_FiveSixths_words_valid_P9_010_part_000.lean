-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_010_part_000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:52:27.362711+00:00
-- url     : https://prove2.me/submissions/095e4ac8-50a9-450e-bd27-4baaf40e6190

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_200
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_201
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_202
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_203
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_204
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
    (hlo : 2070 ≤ j.val) (hhi : j.val < 2185)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 23, codeFunctionP9 (2070 + i.val) = (witnessP9_200 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 23, codeFunctionP9 (2093 + i.val) = (witnessP9_201 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 23, codeFunctionP9 (2116 + i.val) = (witnessP9_202 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 23, codeFunctionP9 (2139 + i.val) = (witnessP9_203 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 23, codeFunctionP9 (2162 + i.val) = (witnessP9_204 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_5 : j.val < 2116
  ·
    by_cases h0_2 : j.val < 2093
    ·
      let i : Fin 23 := ⟨j.val - 2070, by omega⟩
      apply of_witness A (witnessP9_200 i) 1800 (RealPinwheel.FiveSixths.checked_P9_200 i).1 (RealPinwheel.FiveSixths.checked_P9_200 i).2
      rw [← align_0 i]
      have he : 2070 + i.val = j.val := by dsimp [i]; omega
      rw [he]
      exact hb
    ·
      let i : Fin 23 := ⟨j.val - 2093, by omega⟩
      apply of_witness A (witnessP9_201 i) 1800 (RealPinwheel.FiveSixths.checked_P9_201 i).1 (RealPinwheel.FiveSixths.checked_P9_201 i).2
      rw [← align_1 i]
      have he : 2093 + i.val = j.val := by dsimp [i]; omega
      rw [he]
      exact hb
  ·
    by_cases h2_5 : j.val < 2139
    ·
      let i : Fin 23 := ⟨j.val - 2116, by omega⟩
      apply of_witness A (witnessP9_202 i) 1800 (RealPinwheel.FiveSixths.checked_P9_202 i).1 (RealPinwheel.FiveSixths.checked_P9_202 i).2
      rw [← align_2 i]
      have he : 2116 + i.val = j.val := by dsimp [i]; omega
      rw [he]
      exact hb
    ·
      by_cases h3_5 : j.val < 2162
      ·
        let i : Fin 23 := ⟨j.val - 2139, by omega⟩
        apply of_witness A (witnessP9_203 i) 1800 (RealPinwheel.FiveSixths.checked_P9_203 i).1 (RealPinwheel.FiveSixths.checked_P9_203 i).2
        rw [← align_3 i]
        have he : 2139 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
      ·
        let i : Fin 23 := ⟨j.val - 2162, by omega⟩
        apply of_witness A (witnessP9_204 i) 1800 (RealPinwheel.FiveSixths.checked_P9_204 i).1 (RealPinwheel.FiveSixths.checked_P9_204 i).2
        rw [← align_4 i]
        have he : 2162 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
