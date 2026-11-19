-- Prove2me | solution 1 for RealPinwheel.FiveSixths.density_certificate_8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:24:37.961901+00:00
-- url     : https://prove2.me/submissions/d2e06cf0-363f-4b79-8d2f-be79717cfe45

import Theorems.Thm_RealPinwheel_FiveSixths_initial_atoms_sound
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D8_0240
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_000
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_001
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_002
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_003
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_004
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_005
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_006
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_007
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_008
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_009
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_010
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_011
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_012
open RealPinwheel.FiveSixths

theorem solution (A : Instance 8) (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  let d : Fin 8 → ℝ := fun i => 1 / A.period i
  have ha : ∀ i, 0 < A.period i := fun i => lt_of_lt_of_le (by norm_num) (A.one_le i)
  have hpos : ∀ i, 0 < d i := fun i => one_div_pos.mpr (ha i)
  have hord : Antitone d := by
    intro i j hij
    exact one_div_le_one_div_of_le (ha i) (A.ordered hij)
  have hsum : (∑ i, if i.val < 8 then d i else 0) ≤ (5 : ℝ) / 6 := by
    simpa [density, d, Fin.sum_univ_succ, add_assoc] using hD
  obtain ⟨j, hb⟩ := RealPinwheel.FiveSixths.covered_fragment_D8_0240 d (initial_atoms_sound d hpos hord hsum)
  by_cases h0_13 : j.val < 890
  ·
    by_cases h0_6 : j.val < 287
    ·
      by_cases h0_3 : j.val < 51
      ·
        exact RealPinwheel.FiveSixths.words_valid_D8_000 A j (by omega) (by omega) hb
      ·
        by_cases h1_3 : j.val < 152
        ·
          exact RealPinwheel.FiveSixths.words_valid_D8_small_001 A j (by omega) (by omega) hb
        ·
          exact RealPinwheel.FiveSixths.words_valid_D8_small_002 A j (by omega) (by omega) hb
    ·
      by_cases h3_6 : j.val < 458
      ·
        exact RealPinwheel.FiveSixths.words_valid_D8_small_003 A j (by omega) (by omega) hb
      ·
        by_cases h4_6 : j.val < 660
        ·
          exact RealPinwheel.FiveSixths.words_valid_D8_small_004 A j (by omega) (by omega) hb
        ·
          exact RealPinwheel.FiveSixths.words_valid_D8_small_005 A j (by omega) (by omega) hb
  ·
    by_cases h6_13 : j.val < 1816
    ·
      by_cases h6_9 : j.val < 1157
      ·
        exact RealPinwheel.FiveSixths.words_valid_D8_small_006 A j (by omega) (by omega) hb
      ·
        by_cases h7_9 : j.val < 1464
        ·
          exact RealPinwheel.FiveSixths.words_valid_D8_small_007 A j (by omega) (by omega) hb
        ·
          exact RealPinwheel.FiveSixths.words_valid_D8_small_008 A j (by omega) (by omega) hb
    ·
      by_cases h9_13 : j.val < 2724
      ·
        by_cases h9_11 : j.val < 2228
        ·
          exact RealPinwheel.FiveSixths.words_valid_D8_small_009 A j (by omega) (by omega) hb
        ·
          exact RealPinwheel.FiveSixths.words_valid_D8_small_010 A j (by omega) (by omega) hb
      ·
        by_cases h11_13 : j.val < 3331
        ·
          exact RealPinwheel.FiveSixths.words_valid_D8_small_011 A j (by omega) (by omega) hb
        ·
          exact RealPinwheel.FiveSixths.words_valid_D8_small_012 A j (by omega) (by omega) hb
