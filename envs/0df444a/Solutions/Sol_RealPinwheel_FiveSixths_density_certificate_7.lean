-- Prove2me | solution 1 for RealPinwheel.FiveSixths.density_certificate_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:07:04.255204+00:00
-- url     : https://prove2.me/submissions/7ddb058f-4626-4f6b-9099-8d05989eba63
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RealPinwheel_FiveSixths_initial_atoms_sound
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D7_0042
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D7_000
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D7_001
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D7_002
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D7_003
open RealPinwheel.FiveSixths

theorem solution (A : Instance 7) (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin 7), 0 < L ∧ L ≤ 352 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  let d : Fin 7 → ℝ := fun i => 1 / A.period i
  have ha : ∀ i, 0 < A.period i := fun i => lt_of_lt_of_le (by norm_num) (A.one_le i)
  have hpos : ∀ i, 0 < d i := fun i => one_div_pos.mpr (ha i)
  have hord : Antitone d := by
    intro i j hij
    exact one_div_le_one_div_of_le (ha i) (A.ordered hij)
  have hsum : (∑ i, if i.val < 7 then d i else 0) ≤ (5 : ℝ) / 6 := by
    simpa [density, d, Fin.sum_univ_succ, add_assoc] using hD
  obtain ⟨j, hb⟩ := RealPinwheel.FiveSixths.covered_fragment_D7_0042 d (initial_atoms_sound d hpos hord hsum)
  by_cases h0_4 : j.val < 558
  ·
    by_cases h0_2 : j.val < 196
    ·
      exact RealPinwheel.FiveSixths.words_valid_D7_000 A j (by omega) (by omega) hb
    ·
      exact RealPinwheel.FiveSixths.words_valid_D7_001 A j (by omega) (by omega) hb
  ·
    by_cases h2_4 : j.val < 1095
    ·
      exact RealPinwheel.FiveSixths.words_valid_D7_002 A j (by omega) (by omega) hb
    ·
      exact RealPinwheel.FiveSixths.words_valid_D7_003 A j (by omega) (by omega) hb
