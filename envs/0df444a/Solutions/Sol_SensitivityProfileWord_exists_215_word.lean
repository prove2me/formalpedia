-- Prove2me | solution 1 for SensitivityProfileWord.exists_215_word
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-10-22T18:50:09.814345+00:00
-- url     : https://prove2.me/submissions/f518449f-684a-4b10-b7d6-acab64c47d96
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SensitivityWordFrontier_search_correct
import Theorems.Thm_SensitivityWordFrontier_exists_215_success

theorem solution :
    ∃ (n : ℕ) (word : List (SensitivityProfileCycle.Recipe (n+1))),
      SensitivityProfileWord.Crosses215 word := by
  obtain ⟨n, k, hs⟩ := SensitivityWordFrontier.exists_215_success
  obtain ⟨word, _hlen, hcross⟩ :=
    (SensitivityWordFrontier.search_correct (n+1) k).mp hs
  exact ⟨n, word, hcross⟩
