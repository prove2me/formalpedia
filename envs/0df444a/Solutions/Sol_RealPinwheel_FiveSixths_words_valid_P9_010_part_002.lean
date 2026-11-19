-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_010_part_002
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:52:27.444961+00:00
-- url     : https://prove2.me/submissions/9f67555c-f268-44b9-849d-3e7335623968

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_210
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_211
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_212
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_213
import Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_214
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
    (hlo : 2305 ≤ j.val) (hhi : j.val < 2430)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  have align_0 : ∀ i : Fin 25, codeFunctionP9 (2305 + i.val) = (witnessP9_210 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_1 : ∀ i : Fin 25, codeFunctionP9 (2330 + i.val) = (witnessP9_211 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_2 : ∀ i : Fin 25, codeFunctionP9 (2355 + i.val) = (witnessP9_212 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_3 : ∀ i : Fin 25, codeFunctionP9 (2380 + i.val) = (witnessP9_213 i).code := by
    intro i
    fin_cases i <;> rfl
  have align_4 : ∀ i : Fin 25, codeFunctionP9 (2405 + i.val) = (witnessP9_214 i).code := by
    intro i
    fin_cases i <;> rfl
  by_cases h0_5 : j.val < 2355
  ·
    by_cases h0_2 : j.val < 2330
    ·
      let i : Fin 25 := ⟨j.val - 2305, by omega⟩
      apply of_witness A (witnessP9_210 i) 1800 (RealPinwheel.FiveSixths.checked_P9_210 i).1 (RealPinwheel.FiveSixths.checked_P9_210 i).2
      rw [← align_0 i]
      have he : 2305 + i.val = j.val := by dsimp [i]; omega
      rw [he]
      exact hb
    ·
      let i : Fin 25 := ⟨j.val - 2330, by omega⟩
      apply of_witness A (witnessP9_211 i) 1800 (RealPinwheel.FiveSixths.checked_P9_211 i).1 (RealPinwheel.FiveSixths.checked_P9_211 i).2
      rw [← align_1 i]
      have he : 2330 + i.val = j.val := by dsimp [i]; omega
      rw [he]
      exact hb
  ·
    by_cases h2_5 : j.val < 2380
    ·
      let i : Fin 25 := ⟨j.val - 2355, by omega⟩
      apply of_witness A (witnessP9_212 i) 1800 (RealPinwheel.FiveSixths.checked_P9_212 i).1 (RealPinwheel.FiveSixths.checked_P9_212 i).2
      rw [← align_2 i]
      have he : 2355 + i.val = j.val := by dsimp [i]; omega
      rw [he]
      exact hb
    ·
      by_cases h3_5 : j.val < 2405
      ·
        let i : Fin 25 := ⟨j.val - 2380, by omega⟩
        apply of_witness A (witnessP9_213 i) 1800 (RealPinwheel.FiveSixths.checked_P9_213 i).1 (RealPinwheel.FiveSixths.checked_P9_213 i).2
        rw [← align_3 i]
        have he : 2380 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
      ·
        let i : Fin 25 := ⟨j.val - 2405, by omega⟩
        apply of_witness A (witnessP9_214 i) 1800 (RealPinwheel.FiveSixths.checked_P9_214 i).1 (RealPinwheel.FiveSixths.checked_P9_214 i).2
        rw [← align_4 i]
        have he : 2405 + i.val = j.val := by dsimp [i]; omega
        rw [he]
        exact hb
