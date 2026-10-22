-- Prove2me | solution 1 for SensitivityProfileSearch.exists_215_orbit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-10-21T22:47:44.150703+00:00
-- url     : https://prove2.me/submissions/14679123-4f94-47ca-ba68-5eaa7665226a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SensitivityProfileWord_orbit_iff_word
import Theorems.Thm_SensitivityProfileWord_exists_215_word

theorem solution :
    ∃ (n p radius : ℕ)
      (recipes : Fin (p+1) → SensitivityProfileCycle.Recipe (n+1))
      (initial : SensitivityProfileSearch.Profile (n+1)),
      1 < radius ∧ radius^43 < (14055^(p+1))^20 ∧
      SensitivityProfileSearch.PositiveUpper initial ∧
      (∀ d, (recipes d).Valid ∧
        ∀ i, 3 ≤ i.val → 0 < (recipes d).tol i → (recipes d).tol i < 6) ∧
      SensitivityProfileSearch.ReturnsWithin recipes initial radius := by
  exact SensitivityProfileWord.orbit_iff_word.mpr
    SensitivityProfileWord.exists_215_word
