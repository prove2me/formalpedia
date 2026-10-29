-- Prove2me | solution 1 for SensitivityVariableWord.exists_215_word
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-10-29T00:22:06.151515+00:00
-- url     : https://prove2.me/submissions/b08fdea1-1f64-432a-8964-ef1a858d8472
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SensitivityGraphCheck_search_iff_word
import Theorems.Thm_SensitivityGraphCheck_exists_215_success

set_option autoImplicit false

theorem solution :
    ∃ (G : SensitivityVariableWord.GraphData) (n : ℕ)
      (word : List (SensitivityProfileCycle.Recipe (n + 1))),
      SensitivityVariableWord.Crosses215 G word := by
  exact SensitivityGraphCheck.search_iff_word.mp
    SensitivityGraphCheck.exists_215_success
