-- Prove2me | solution 1 for RealPinwheel.FiveSixths.bounded_potential_base
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:51:08.633801+00:00
-- url     : https://prove2.me/submissions/f35dc899-b08a-4044-b350-0d42e4b6b50a

import Theorems.Thm_RealPinwheel_FiveSixths_initial_atoms_sound
import Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_1442
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_000
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_001
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_002
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_003
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_004
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_005
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_006
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_007
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_008
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_009
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_010
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_011
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_012
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_013
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_014
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_015
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_016
open RealPinwheel.FiveSixths

theorem solution (A : Instance 9) (hD : potential A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  let d : Fin 9 → ℝ := fun i => 1 / A.period i
  have ha : ∀ i, 0 < A.period i := fun i => lt_of_lt_of_le (by norm_num) (A.one_le i)
  have hpos : ∀ i, 0 < d i := fun i => one_div_pos.mpr (ha i)
  have hord : Antitone d := by
    intro i j hij
    exact one_div_le_one_div_of_le (ha i) (A.ordered hij)
  have hsum : (∑ i, if i.val < 8 then d i else 0) ≤ (5 : ℝ) / 6 := by
    simpa [potential, d, Fin.sum_univ_succ, add_assoc] using hD
  obtain ⟨j, hb⟩ := RealPinwheel.FiveSixths.covered_fragment_P9_1442 d (initial_atoms_sound d hpos hord hsum)
  by_cases h0_17 : j.val < 1302
  ·
    by_cases h0_8 : j.val < 362
    ·
      by_cases h0_4 : j.val < 113
      ·
        by_cases h0_2 : j.val < 32
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_000 A j (by omega) (by omega) hb
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_001 A j (by omega) (by omega) hb
      ·
        by_cases h2_4 : j.val < 223
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_002 A j (by omega) (by omega) hb
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_003 A j (by omega) (by omega) hb
    ·
      by_cases h4_8 : j.val < 746
      ·
        by_cases h4_6 : j.val < 532
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_004 A j (by omega) (by omega) hb
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_005 A j (by omega) (by omega) hb
      ·
        by_cases h6_8 : j.val < 1002
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_006 A j (by omega) (by omega) hb
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_007 A j (by omega) (by omega) hb
  ·
    by_cases h8_17 : j.val < 3108
    ·
      by_cases h8_12 : j.val < 2070
      ·
        by_cases h8_10 : j.val < 1654
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_008 A j (by omega) (by omega) hb
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_009 A j (by omega) (by omega) hb
      ·
        by_cases h10_12 : j.val < 2558
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_010 A j (by omega) (by omega) hb
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_011 A j (by omega) (by omega) hb
    ·
      by_cases h12_17 : j.val < 4511
      ·
        by_cases h12_14 : j.val < 3756
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_012 A j (by omega) (by omega) hb
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_013 A j (by omega) (by omega) hb
      ·
        by_cases h14_17 : j.val < 5415
        ·
          exact RealPinwheel.FiveSixths.words_valid_P9_014 A j (by omega) (by omega) hb
        ·
          by_cases h15_17 : j.val < 6561
          ·
            exact RealPinwheel.FiveSixths.words_valid_P9_015 A j (by omega) (by omega) hb
          ·
            exact RealPinwheel.FiveSixths.words_valid_P9_016 A j (by omega) (by omega) hb
