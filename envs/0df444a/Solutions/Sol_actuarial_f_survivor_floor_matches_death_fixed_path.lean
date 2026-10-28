-- Prove2me | solution 1 for actuarial_f_survivor_floor_matches_death_fixed_path
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:40:57.607399+00:00
-- url     : https://prove2.me/submissions/ccc2dde0-f729-411b-a9cb-d1e19bae4aab

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseBaseAtDeath
import Definitions.Def_actuarial_f_spouseInstalment
import Definitions.Def_actuarial_f_survivorFlooredInstalment

open ActuarialUnderpinsF

theorem solution
    (h z i j t : ℕ) (sa sb : ℕ → ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) :
    survivorFlooredInstalment h z i j t sa sb gs =
      spouseInstalment h z i j t
        (fun z i => spouseBaseAtDeath z i sa sb) gs := by
  rfl
