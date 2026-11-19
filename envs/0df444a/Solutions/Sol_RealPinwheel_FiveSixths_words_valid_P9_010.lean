-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_P9_010
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:53:27.381749+00:00
-- url     : https://prove2.me/submissions/a11e66aa-55c7-47b7-9246-c67cb0b402f7

import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_010_part_000
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_010_part_001
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_010_part_002
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_010_part_003
open RealPinwheel.FiveSixths

theorem solution (A : Instance 9) (j : Fin 7968)
    (hlo : 2070 ≤ j.val) (hhi : j.val < 2558)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by
  by_cases h0_4 : j.val < 2305
  ·
    by_cases h0_2 : j.val < 2185
    ·
      exact RealPinwheel.FiveSixths.words_valid_P9_010_part_000 A j (by omega) (by omega) hb
    ·
      exact RealPinwheel.FiveSixths.words_valid_P9_010_part_001 A j (by omega) (by omega) hb
  ·
    by_cases h2_4 : j.val < 2430
    ·
      exact RealPinwheel.FiveSixths.words_valid_P9_010_part_002 A j (by omega) (by omega) hb
    ·
      exact RealPinwheel.FiveSixths.words_valid_P9_010_part_003 A j (by omega) (by omega) hb
