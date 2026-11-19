-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_010_part_003
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:52:39.812634+00:00
-- url     : https://prove2.me/submissions/cd80d7a6-94fa-4213-8e6a-7893b07c475c

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_215
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_216
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_217
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_218
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_219
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
    (hlo : 2430 ≤ j.val) (hhi : j.val < 2558)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 25, codeFunctionP9 (2430 + i.val) = (witnessP9_215 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 25, codeFunctionP9 (2455 + i.val) = (witnessP9_216 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 26, codeFunctionP9 (2480 + i.val) = (witnessP9_217 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 26, codeFunctionP9 (2506 + i.val) = (witnessP9_218 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 26, codeFunctionP9 (2532 + i.val) = (witnessP9_219 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_5 : j.val < 2480
  ·
    by_cases h0_2 : j.val < 2455
    ·
      let i : Fin 25 := ⟨j.val - 2430, by omega⟩
      apply of_witness A (witnessP9_215 i) 1800 (RealPinwheel.FiveSixths.checked_P9_215 i).1 (RealPinwheel.FiveSixths.checked_P9_215 i).2
      rw [← align_0 i]
      have he : 2430 + i.val = j.val := by dsimp [i]; omega
      rw [he]
      exact hb
    ·
      let i : Fin 25 := ⟨j.val - 2455, by omega⟩
      apply of_witness A (witnessP9_216 i) 1800 (RealPinwheel.FiveSixths.checked_P9_216 i).1 (RealPinwheel.FiveSixths.checked_P9_216 i).2
      rw [← align_1 i]
      have he : 2455 + i.val = j.val := by dsimp [i]; omega
      rw [he]
      exact hb
  ·
    by_cases h2_5 : j.val < 2506
    ·
      let i : Fin 26 := ⟨j.val - 2480, by omega⟩
      apply of_witness A (witnessP9_217 i) 1800 (RealPinwheel.FiveSixths.checked_P9_217 i).1 (RealPinwheel.FiveSixths.checked_P9_217 i).2
      rw [← align_2 i]
      have he : 2480 + i.val = j.val := by dsimp [i]; omega
      rw [he]
      exact hb
    ·
      by_cases h3_5 : j.val < 2532
      ·
        let i : Fin 26 := ⟨j.val - 2506, by omega⟩
        apply of_witness A (witnessP9_218 i) 1800 (RealPinwheel.FiveSixths.checked_P9_218 i).1 (RealPinwheel.FiveSixths.checked_P9_218 i).2
        rw [← align_3 i]
        have he : 2506 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
      ·
        let i : Fin 26 := ⟨j.val - 2532, by omega⟩
        apply of_witness A (witnessP9_219 i) 1800 (RealPinwheel.FiveSixths.checked_P9_219 i).1 (RealPinwheel.FiveSixths.checked_P9_219 i).2
        rw [← align_4 i]
        have he : 2532 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
