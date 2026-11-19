-- Prove2me | solution 1 for RealPinwheel.FiveSixths.words_valid_D8_001
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:34:19.937765+00:00
-- url     : https://prove2.me/submissions/77708482-ef3f-4744-a44e-97b332852acc

import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_010
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_011
import Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_012
open RealPinwheel.FiveSixths
theorem solution (A : Instance 8) (j : Fin 3725)
    (hlo : 2228 ≤ j.val) (hhi : j.val < 3725)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S  := by
  by_cases h0 : j.val < 2724
  · exact RealPinwheel.FiveSixths.words_valid_D8_small_010 A j (by omega) (by omega) hb
  ·
    by_cases h1 : j.val < 3331
    · exact RealPinwheel.FiveSixths.words_valid_D8_small_011 A j (by omega) (by omega) hb
    ·
      exact RealPinwheel.FiveSixths.words_valid_D8_small_012 A j (by omega) (by omega) hb
